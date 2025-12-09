/* p_unix.cpp --

   This file is part of the UPX executable compressor.

   Copyright (C) 1996-2025 Markus Franz Xaver Johannes Oberhumer
   Copyright (C) 1996-2025 Laszlo Molnar
   Copyright (C) 2000-2025 John F. Reiser
   All Rights Reserved.

   UPX and the UCL library are free software; you can redistribute them
   and/or modify them under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of
   the License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; see the file COPYING.
   If not, write to the Free Software Foundation, Inc.,
   59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

   Markus F.X.J. Oberhumer              Laszlo Molnar
   <markus@oberhumer.com>               <ezerotven+github@gmail.com>

   John F. Reiser
   <jreiser@users.sourceforge.net>
 */


#include "conf.h"

#include "file.h"
#include "filter.h"
#include "packer.h"
#include "p_unix.h"
#include "p_elf.h"

// Lightweight obfuscation stream cipher (TEA-derived) for encrypting block data.
// Key is derived from a 16-byte salt (per file) plus block index.
namespace {

static void derive_key(const unsigned char salt[16], uint32_t block_index, uint32_t k[4]) {
    for (int i = 0; i < 4; ++i) {
        k[i] =  (uint32_t)salt[i*4 + 0]
              | (uint32_t)salt[i*4 + 1] << 8
              | (uint32_t)salt[i*4 + 2] << 16
              | (uint32_t)salt[i*4 + 3] << 24;
    }
    k[0] ^= 0x9e3779b9u ^ block_index;
    k[1] ^= 0x7f4a7c15u ^ (block_index << 7);
    k[2] ^= 0x3c6ef372u ^ (block_index >> 3);
    k[3] ^= 0xbb67ae85u ^ (block_index << 13);
}

static void tea_keystream(uint32_t counter, const uint32_t k[4], unsigned char out[8]) {
    uint32_t v0 = counter;
    uint32_t v1 = counter ^ 0xdeadbeefu;
    uint32_t sum = 0;
    const uint32_t delta = 0x9e3779b9u;
    for (unsigned i = 0; i < 16; ++i) {
        sum += delta;
        v0 += ((v1 << 4) + k[0]) ^ (v1 + sum) ^ ((v1 >> 5) + k[1]);
        v1 += ((v0 << 4) + k[2]) ^ (v0 + sum) ^ ((v0 >> 5) + k[3]);
    }
    out[0] = (unsigned char)(v0);
    out[1] = (unsigned char)(v0 >> 8);
    out[2] = (unsigned char)(v0 >> 16);
    out[3] = (unsigned char)(v0 >> 24);
    out[4] = (unsigned char)(v1);
    out[5] = (unsigned char)(v1 >> 8);
    out[6] = (unsigned char)(v1 >> 16);
    out[7] = (unsigned char)(v1 >> 24);
}

static void encrypt_buffer(const unsigned char salt[16], uint32_t block_index,
                           unsigned char *buf, unsigned len) {
    if (len == 0) return;
    uint32_t k[4];
    derive_key(salt, block_index, k);
    uint32_t counter = 0;
    unsigned pos = 0;
    unsigned char ks[8];
    while (pos < len) {
        tea_keystream(counter++, k, ks);
        unsigned chunk = (len - pos) < 8 ? (len - pos) : 8;
        for (unsigned i = 0; i < chunk; ++i) {
            buf[pos + i] ^= ks[i];
        }
        pos += chunk;
    }
}

static unsigned char g_enc_salt[16];
static bool g_enc_salt_valid = false;
}

static void decrypt_buffer(const unsigned char salt[16], uint32_t block_index,
                           unsigned char *buf, unsigned len) {
    if (len == 0) return;
    uint32_t k[4];
    derive_key(salt, block_index, k);
    uint32_t counter = 0;
    unsigned pos = 0;
    unsigned char ks[8];
    while (pos < len) {
        tea_keystream(counter++, k, ks);
        unsigned chunk = (len - pos) < 8 ? (len - pos) : 8;
        for (unsigned i = 0; i < chunk; ++i) {
            buf[pos + i] ^= ks[i];
        }
        pos += chunk;
    }
}

// do not change
#define BLOCKSIZE       (512*1024)


/*************************************************************************
//
**************************************************************************/

PackUnix::PackUnix(InputFile *f) :
    super(f), exetype(0), blocksize(0), overlay_offset(0), lsize(0),
    methods_used(0), szb_info(sizeof(b_info))
{
    COMPILE_TIME_ASSERT(sizeof(Elf32_Ehdr) == 52)
    COMPILE_TIME_ASSERT(sizeof(Elf32_Phdr) == 32)
    COMPILE_TIME_ASSERT(sizeof(b_info) == 12)
    COMPILE_TIME_ASSERT(sizeof(l_info) == 12)
    COMPILE_TIME_ASSERT(sizeof(p_info) == 12)

    // opt->o_unix.android_shlib is global, but must be hint
    // that applies only when an actual ET_DYN on EM_ARM (only!).
    // User might say "--android-shlib" but give mulitple files
    // where some are ET_EXEC.
    saved_opt_android_shlib = opt->o_unix.android_shlib;
    opt->o_unix.android_shlib = 0;  // Must apply selectively
    // Besides, cannot figure out why asl_slide_Shdrs does not work.
}

PackUnix::~PackUnix()
{
    opt->o_unix.android_shlib = saved_opt_android_shlib;
}

// common part of canPack(), enhanced by subclasses
tribool PackUnix::canPack()
{
    if (exetype == 0)
        return false;

#if defined(__unix__)
    // must be executable by owner
    if ((fi->st.st_mode & S_IXUSR) == 0)
        throwCantPack("file not executable; try 'chmod +x'");
#endif
    if (file_size < 4096)
        throwCantPack("file is too small");

    // info: currently the header is 36 (32+4) bytes before EOF
    unsigned char buf[256];
    fi->seek(-(off_t)sizeof(buf), SEEK_END);
    fi->readx(buf, sizeof(buf));
    checkAlreadyPacked(buf, sizeof(buf));

    return true;
}


void PackUnix::writePackHeader(OutputFile *fo)
{
    unsigned char buf[32];
    memset(buf, 0, sizeof(buf));

    const int hsize = ph.getPackHeaderSize();
    assert((unsigned)hsize <= sizeof(buf));

    // note: magic constants are always le32
    set_le32(buf+0, UPX_MAGIC_LE32);
    set_le32(buf+4, UPX_MAGIC2_LE32);

    checkPatch(nullptr, 0, 0, 0);  // reset
    patchPackHeader(buf, hsize);
    checkPatch(nullptr, 0, 0, 0);  // reset

    fo->write(buf, hsize);
}


/*************************************************************************
// Generic Unix pack(). Subclasses must provide patchLoader().
//
// A typical compressed Unix executable looks like this:
//   - loader stub
//   - 12 bytes header info
//   - the compressed blocks, each with a 8 byte header for block sizes
//   - 4 bytes block end marker (uncompressed size 0)
//   - 32 bytes UPX packheader
//   - 4 bytes overlay offset (needed for decompression)
**************************************************************************/

// see note below and Packer::compress()
bool PackUnix::checkCompressionRatio(unsigned, unsigned) const
{
    return true;
}

void PackUnix::pack1(OutputFile * /*fo*/, Filter & /*ft*/)
{
    // derived class usually provides this
}

int PackUnix::getStrategy(Filter &/*ft*/)
{
    // Called just before reading and compressing each block.
    // Might want to adjust blocksize, etc.

    // If user specified the filter, then use it (-2==filter_strategy).
    // Else try the first two filters, and pick the better (2==filter_strategy).
    return (opt->no_filter ? -3 : ((opt->filter > 0) ? -2 : 2));
}

int PackUnix::pack2(OutputFile *fo, Filter &ft)
{
    // compress blocks
    total_in = 0;
    total_out = 0;

// FIXME: ui_total_passes is not correct with multiple blocks...
//    ui_total_passes = (file_size + blocksize - 1) / blocksize;
//    if (ui_total_passes == 1)
//        ui_total_passes = 0;

    unsigned remaining = file_size;
    unsigned n_block = 0;
    while (remaining > 0)
    {
        uint32_t enc_block_index = n_block;
        // FIXME: disable filters if we have more than one block.
        // FIXME: There is only 1 un-filter in the stub [as of 2002-11-10].
        // So the next block really has no choice!
        // This merely prevents an assert() in compressWithFilters(),
        // which assumes it has free choice on each call [block].
        // And if the choices aren't the same on each block,
        // then un-filtering will give incorrect results.
        int filter_strategy = getStrategy(ft);
        if (file_size > (off_t)blocksize)
            filter_strategy = -3;      // no filters

        int l = fi->readx(ibuf, UPX_MIN(blocksize, remaining));
        remaining -= l;

        // Note: compression for a block can fail if the
        //       file is e.g. blocksize + 1 bytes long

        // compress
        ph.overlap_overhead = 0;
        ph.c_len = ph.u_len = l;
        ft.buf_len = l;

        // compressWithFilters() updates u_adler _inside_ compress();
        // that is, AFTER filtering.  We want BEFORE filtering,
        // so that decompression checks the end-to-end checksum.
        unsigned const end_u_adler = upx_adler32(ibuf, ph.u_len, ph.u_adler);
        compressWithFilters(&ft, OVERHEAD, NULL_cconf, filter_strategy,
            !!n_block++);  // check compression ratio only on first block

        if (ph.c_len < ph.u_len) {
            const upx_bytep tbuf = nullptr;
            if (ft.id == 0) tbuf = ibuf;
            ph.overlap_overhead = OVERHEAD;
            if (!testOverlappingDecompression(obuf, tbuf, ph.overlap_overhead)) {
                // not in-place compressible
                ph.c_len = ph.u_len;
            }
        }
        if (ph.c_len >= ph.u_len) {
            // block is not compressible
            ph.c_len = ph.u_len;
            // must manually update checksum of compressed data
            ph.c_adler = upx_adler32(ibuf, ph.u_len, ph.saved_c_adler);
        }

        // write block header
        b_info blk_info;
        memset(&blk_info, 0, sizeof(blk_info));
        set_te32(&blk_info.sz_unc, ph.u_len);
        set_te32(&blk_info.sz_cpr, ph.c_len);
        if (ph.c_len < ph.u_len) {
            blk_info.b_method = (unsigned char) ph.method;
            blk_info.b_ftid = (unsigned char) ph.filter;
            blk_info.b_cto8 = (unsigned char) ph.filter_cto;
        }
        fo->write(&blk_info, sizeof(blk_info));
        b_len += sizeof(b_info);

        // write compressed data
        if (ph.c_len < ph.u_len) {
            if (g_enc_salt_valid) {
                // Encrypt in place, write, then decrypt back to restore buffer
                encrypt_buffer(g_enc_salt, enc_block_index, obuf, ph.c_len);
                fo->write(obuf, ph.c_len);
                decrypt_buffer(g_enc_salt, enc_block_index, obuf, ph.c_len);
            } else {
                fo->write(obuf, ph.c_len);
            }
            verifyOverlappingDecompression();  // uses ph.u_adler
        }
        else {
            if (g_enc_salt_valid) {
                // Encrypt in place, write, then decrypt back to restore buffer
                encrypt_buffer(g_enc_salt, enc_block_index, ibuf, ph.u_len);
                fo->write(ibuf, ph.u_len);
                decrypt_buffer(g_enc_salt, enc_block_index, ibuf, ph.u_len);
            } else {
                fo->write(ibuf, ph.u_len);
            }
        }
        ph.u_adler = end_u_adler;

        total_in += ph.u_len;
        total_out += ph.c_len;
    }

    // update header with totals
    ph.u_len = total_in;
    ph.c_len = total_out;

    if ((off_t)total_in != file_size) {
        throwEOFException();
    }

    return 1;  // default: write end-of-compression bhdr next
}

void
PackUnix::patchLoaderChecksum()
{
    unsigned char *const ptr = getLoader();
    l_info *const lp = &linfo;
    // checksum for loader; also some PackHeader info
    lp->l_magic = UPX_MAGIC_LE32;  // LE32 always
    set_te16(&lp->l_lsize, (upx_uint16_t) lsize);
    lp->l_version = (unsigned char) ph.version;
    lp->l_format  = (unsigned char) ph.format;
    // INFO: lp->l_checksum is currently unused
    set_te32(&lp->l_checksum, upx_adler32(ptr, lsize));
}

off_t PackUnix::pack3(OutputFile *fo, Filter &ft)
{
    if (nullptr==linker) {
        // If no filter, then linker is not constructed by side effect
        // of packExtent calling compressWithFilters.
        // This is typical after "/usr/bin/patchelf --set-rpath".
        buildLoader(&ft);
    }
    upx_byte *p = getLoader();
    lsize = getLoaderSize();
    updateLoader(fo);
    patchLoaderChecksum();
    fo->write(p, lsize);
    return fo->getBytesWritten();
}

void PackUnix::pack4(OutputFile *fo, Filter &)
{
    writePackHeader(fo);

    unsigned tmp;
    set_te32(&tmp, overlay_offset);
    fo->write(&tmp, sizeof(tmp));
}

void PackUnix::pack(OutputFile *fo)
{
    Filter ft(ph.level);
    ft.addvalue = 0;
    b_len = 0;
    progid = 0;

    // set options
    blocksize = opt->o_unix.blocksize;
    if (blocksize <= 0)
        blocksize = BLOCKSIZE;
    if ((off_t)blocksize > file_size)
        blocksize = file_size;

    // init compression buffers
    ibuf.alloc(blocksize);
    obuf.allocForCompression(blocksize);

    fi->seek(0, SEEK_SET);
    pack1(fo, ft);  // generate Elf header, etc.

    // Shlib probably did not generate Elf header yet.
    if (fo->st_size()) { // Only append if pack1 actually wrote something.
        p_info hbuf;
        set_te32(&hbuf.p_progid, progid);
        set_te32(&hbuf.p_filesize, file_size);
        set_te32(&hbuf.p_blocksize, blocksize);
        fo->write(&hbuf, sizeof(hbuf));
    }

    g_enc_salt_valid = (ph.format == UPX_F_LINUX_ELF_i386 || ph.format == UPX_F_LINUX_i386
        || ph.format == UPX_F_LINUX_ELF64_AMD64);
    if (g_enc_salt_valid) {
        for (unsigned i = 0; i < sizeof(g_enc_salt); ++i) {
            g_enc_salt[i] = (unsigned char)(upx_rand() & 0xff);
        }
        fo->write(g_enc_salt, sizeof(g_enc_salt));
    }

    // append the compressed body
    if (pack2(fo, ft)) {
        // write block end marker (uncompressed size 0)
        b_info hdr; memset(&hdr, 0, sizeof(hdr));
        set_le32(&hdr.sz_cpr, UPX_MAGIC_LE32);
        fo->write(&hdr, sizeof(hdr));
    }

    pack3(fo, ft);  // append loader

    pack4(fo, ft);  // append PackHeader and overlay_offset; update Elf header

    // finally check the compression ratio
    if (!checkFinalCompressionRatio(fo))
        throwNotCompressible();
}


void PackUnix::packExtent(
    const Extent &x,
    Filter *ft,
    OutputFile *fo,
    unsigned hdr_u_len,
    unsigned b_extra,
    bool inhibit_compression_check
)
{
    unsigned const init_u_adler = ph.u_adler;
    unsigned const init_c_adler = ph.c_adler;
    MemBuffer hdr_ibuf;
    if (hdr_u_len) {
        hdr_ibuf.alloc(hdr_u_len);
        fi->seek(0, SEEK_SET);
        int l = fi->readx(hdr_ibuf, hdr_u_len);
        (void)l;
    }
    fi->seek(x.offset, SEEK_SET);
    for (off_t rest = x.size; 0 != rest; ) {
        int const filter_strategy = ft ? getStrategy(*ft) : 0;
        int l = fi->readx(ibuf, UPX_MIN(rest, (off_t)blocksize));
        if (l == 0) {
            break;
        }
        rest -= l;

        // Note: compression for a block can fail if the
        //       file is e.g. blocksize + 1 bytes long

        // compress
        ph.c_len = ph.u_len = l;
        ph.overlap_overhead = 0;
        unsigned end_u_adler = 0;
        if (ft) {
            // compressWithFilters() updates u_adler _inside_ compress();
            // that is, AFTER filtering.  We want BEFORE filtering,
            // so that decompression checks the end-to-end checksum.
            end_u_adler = upx_adler32(ibuf, ph.u_len, ph.u_adler);
            ft->buf_len = l;

                // compressWithFilters() requirements?
            ph.filter = 0;
            ph.filter_cto = 0;
            ft->id = 0;
            ft->cto = 0;

            compressWithFilters(ft, OVERHEAD, NULL_cconf, filter_strategy,
                                0, 0, 0, hdr_ibuf, hdr_u_len, inhibit_compression_check);
        }
        else {
            (void) compress(ibuf, ph.u_len, obuf);    // ignore return value
        }

        if (ph.c_len < ph.u_len) {
            const upx_bytep tbuf = nullptr;
            if (ft == nullptr || ft->id == 0) tbuf = ibuf;
            ph.overlap_overhead = OVERHEAD;
            if (!testOverlappingDecompression(obuf, tbuf, ph.overlap_overhead)) {
                // not in-place compressible
                ph.c_len = ph.u_len;
            }
        }
        if (ph.c_len >= ph.u_len) {
            // block is not compressible
            ph.c_len = ph.u_len;
            memcpy(obuf, ibuf, ph.c_len);
            // must update checksum of compressed data
            ph.c_adler = upx_adler32(ibuf, ph.u_len, ph.c_adler);
        }

        // write block sizes
        b_info tmp;
        if (hdr_u_len) {
            unsigned hdr_c_len = 0;
            MemBuffer hdr_obuf;
            hdr_obuf.allocForCompression(hdr_u_len);
            int r = upx_compress(hdr_ibuf, hdr_u_len, hdr_obuf, &hdr_c_len,
                /* &progress callback */ nullptr,
                ph_forced_method(ph.method), 10,
                /* &config_t */ nullptr, /* &result_t */ nullptr);
            if (r != UPX_E_OK)
                throwInternalError("header compression failed");
            if (hdr_c_len >= hdr_u_len)
                throwInternalError("header compression size increase");
            ph.saved_u_adler = upx_adler32(hdr_ibuf, hdr_u_len, init_u_adler);
            ph.saved_c_adler = upx_adler32(hdr_obuf, hdr_c_len, init_c_adler);
            ph.u_adler = upx_adler32(ibuf, ph.u_len, ph.saved_u_adler);
            ph.c_adler = upx_adler32(obuf, ph.c_len, ph.saved_c_adler);
            end_u_adler = ph.u_adler;
            memset(&tmp, 0, sizeof(tmp));
            set_te32(&tmp.sz_unc, hdr_u_len);
            set_te32(&tmp.sz_cpr, hdr_c_len);
            tmp.b_method = (unsigned char) ph_forced_method(ph.method);
            tmp.b_extra = b_extra;
            fo->write(&tmp, sizeof(tmp));
            total_out += sizeof(tmp);
            b_len += sizeof(b_info);
            fo->write(hdr_obuf, hdr_c_len);
            total_out += hdr_c_len;
            total_in  += hdr_u_len;
            hdr_u_len = 0;  // compress hdr one time only
        }
        memset(&tmp, 0, sizeof(tmp));
        set_te32(&tmp.sz_unc, ph.u_len);
        set_te32(&tmp.sz_cpr, ph.c_len);
        if (ph.c_len < ph.u_len) {
            tmp.b_method = (unsigned char) ph.method;
            if (ft) {
                tmp.b_ftid = (unsigned char) ft->id;
                tmp.b_cto8 = ft->cto;
            }
        }
        tmp.b_extra = b_extra;
        fo->write(&tmp, sizeof(tmp));
        total_out += sizeof(tmp);
        b_len += sizeof(b_info);

        if (ft) {
            ph.u_adler = end_u_adler;
        }
        // write compressed data
        if (ph.c_len < ph.u_len) {
            fo->write(obuf, ph.c_len);
            total_out += ph.c_len;
            // Checks ph.u_adler after decompression, after unfiltering
            verifyOverlappingDecompression(ft);
        }
        else {
            fo->write(ibuf, ph.u_len);
            total_out += ph.u_len;
        }

        total_in += ph.u_len;
    }
}

// Consumes b_info header block and sz_cpr data block from input file 'fi'.
// De-compresses; appends to output file 'fo' unless rewrite or peeking.
// For "peeking" without writing: set (fo = nullptr), (is_rewrite = -1)
// Return actual length when peeking; else 0.
unsigned PackUnix::unpackExtent(unsigned wanted, OutputFile *fo,
    unsigned &c_adler, unsigned &u_adler,
    bool first_PF_X,
    int is_rewrite // 0(false): write; 1(true): rewrite; -1: no write
)
{
    b_info hdr; memset(&hdr, 0, sizeof(hdr));
    unsigned inlen = 0; // output index (if-and-only-if peeking)
    while (wanted) {
        fi->readx(&hdr, szb_info);
        int const sz_unc = ph.u_len = get_te32(&hdr.sz_unc);
        int const sz_cpr = ph.c_len = get_te32(&hdr.sz_cpr);
        ph.filter_cto = hdr.b_cto8;

        if (sz_unc == 0 || M_LZMA < hdr.b_method) {
            throwCantUnpack("corrupt b_info");
            break;
        }
        if (sz_unc <= 0 || sz_cpr <= 0)
            throwCantUnpack("corrupt b_info");
        if (sz_cpr > sz_unc || sz_unc > (int)blocksize)
            throwCantUnpack("corrupt b_info");

        // place the input for overlapping de-compression
        int j = inlen + sz_unc + OVERHEAD - sz_cpr;
        if (ibuf.getSize() < (unsigned)(j + sz_cpr)) {
            throwCantUnpack("corrupt b_info");
        }
        fi->readx(ibuf+j, sz_cpr);
        total_in += sz_cpr;
        // update checksum of compressed data
        c_adler = upx_adler32(ibuf + j, sz_cpr, c_adler);

        if (sz_cpr < sz_unc) { // block was compressed
            ph.set_method(hdr.b_method);
            decompress(ibuf+j, ibuf+inlen, false);
            if (12==szb_info) { // modern per-block filter
                if (hdr.b_ftid) {
                    Filter ft(ph.level);  // FIXME: ph.level for b_info?
                    ft.init(hdr.b_ftid, 0);
                    ft.cto = hdr.b_cto8;
                    ft.unfilter(ibuf+inlen, sz_unc);
                }
            }
            else { // ancient per-file filter
                if (first_PF_X) { // Elf32_Ehdr is never filtered
                    first_PF_X = false;  // but everything else might be
                }
                else if (ph.filter) {
                    Filter ft(ph.level);
                    ft.init(ph.filter, 0);
                    ft.cto = (unsigned char) ph.filter_cto;
                    ft.unfilter(ibuf+inlen, sz_unc);
                }
            }
        }
        else if (sz_cpr == sz_unc) { // slide literal (non-compressible) block
            memmove(&ibuf[inlen], &ibuf[j], sz_unc);
        }
        // update checksum of uncompressed data
        u_adler = upx_adler32(ibuf + inlen, sz_unc, u_adler);
        // write block
        if (fo) {
            if (is_rewrite) {
                fo->rewrite(ibuf, sz_unc);
            }
            else {
                fo->write(ibuf, sz_unc);
                total_out += sz_unc;
            }
        }
        else if (is_rewrite < 0) { // append to &ibuf[inlen]
            inlen += sz_unc;  // accounting; data is already there
            if (wanted <= (unsigned)sz_unc)  // done
                break;
        }
        else if (wanted < (unsigned)sz_unc) // mismatched end-of-block
            throwCantUnpack("corrupt b_info");
        else { // "upx -t": (!fo && !(is_rewrite < 0))
            // No output.
        }
        wanted -= sz_unc;
    }
    return inlen;
}

/*************************************************************************
// Generic Unix canUnpack().
**************************************************************************/

// The prize is the value of overlay_offset: the offset of compressed data
tribool PackUnix::canUnpack()
{
    int const small = 32 + sizeof(overlay_offset);
    // Allow zero-filled last page, for Mac OS X code signing.
    int bufsize = 2*4096 + 2*small +1;
    if (bufsize > fi->st_size())
        bufsize = fi->st_size();
    MemBuffer buf(bufsize);

    fi->seek(-(off_t)bufsize, SEEK_END);
    fi->readx(buf, bufsize);
    return find_overlay_offset(buf);
}

int PackUnix::find_overlay_offset(MemBuffer const &buf)
{
    int const small = 32 + sizeof(overlay_offset);
    int const bufsize = buf.getSize();
    int i = bufsize;
    while (i > small && 0 == buf[--i]) { }
    i -= small;
    // allow incompressible extents
    if (i < 0 || !getPackHeader(buf + i, bufsize - i, true))
        return false;

    int l = ph.buf_offset + ph.getPackHeaderSize();
    if (l < 0 || i + l + 4 > bufsize)
        throwCantUnpack("file corrupted");
    overlay_offset = get_te32(buf + i + l);
    
    // For encrypted formats, add salt size to overlay calculations
    bool uses_salt = (ph.format == UPX_F_LINUX_ELF_i386 || ph.format == UPX_F_LINUX_i386
        || ph.format == UPX_F_LINUX_ELF64_AMD64);
    if (uses_salt) {
        // overlay_offset points to p_info, and salt comes after p_info (12 bytes)
        // No adjustment needed here - overlay_offset is correct
    }
    
    if ((off_t)overlay_offset >= file_size)
        throwCantUnpack("file corrupted");

    return true;
}

/*************************************************************************
// Generic Unix unpack().
//
// This code looks much like the one in stub/l_linux.c
// See notes there.
**************************************************************************/

void PackUnix::unpack(OutputFile *fo)
{
    b_info bhdr;
    unsigned c_adler = upx_adler32(nullptr, 0);
    unsigned u_adler = upx_adler32(nullptr, 0);

    if (ph.version <= 11) {
        szb_info = sizeof(bhdr.sz_unc) + sizeof(bhdr.sz_cpr);  // old style
    }
    // defaults for ph.version == 8
    unsigned orig_file_size = 0;
    blocksize = 512 * 1024;

    fi->seek(overlay_offset, SEEK_SET);
    if (ph.version > 8)
    {
        p_info hbuf;
        fi->readx(&hbuf, sizeof(hbuf));
        orig_file_size = get_te32(&hbuf.p_filesize);
        blocksize = get_te32(&hbuf.p_blocksize);
        off_t max_inflated = file_size * 273;  // zlib limit (256 + 16 + 1)

        if (max_inflated < orig_file_size
        ||  max_inflated < blocksize
        ||  file_size > (off_t)orig_file_size
        ||  blocksize > orig_file_size) {
            throwCantUnpack("file header corrupted");
        }
    }
    else
    {
        // skip 4 bytes (program id)
        fi->seek(4, SEEK_CUR);
    }

    bool dec_use_salt = (ph.format == UPX_F_LINUX_ELF_i386 || ph.format == UPX_F_LINUX_i386
        || ph.format == UPX_F_LINUX_ELF64_AMD64);
    uint32_t dec_block_index = 0;
    if (dec_use_salt) {
        unsigned char saltbuf[16];
        fi->readx(saltbuf, sizeof(saltbuf));
        memcpy(g_enc_salt, saltbuf, sizeof(g_enc_salt));
    }

    if ((int)(blocksize + OVERHEAD) < 0)
        throwCantUnpack("blocksize corrupted");
    ibuf.alloc(blocksize + OVERHEAD);

    // decompress blocks
    total_in = 0;
    total_out = 0;
    memset(&bhdr, 0, sizeof(bhdr));
    for (;;)
    {
#define buf ibuf
        int i;
        unsigned sz_unc, sz_cpr;

        fi->readx(&bhdr, szb_info);
        ph.u_len = sz_unc = get_te32(&bhdr.sz_unc);
        ph.c_len = sz_cpr = get_te32(&bhdr.sz_cpr);
        if (szb_info < sizeof(b_info)) { // some upx version 11
            bhdr.b_method = ph.method;
            bhdr.b_ftid = ph.filter;
            bhdr.b_cto8 = ph.filter_cto;
        }

        if (sz_unc == 0)                   // uncompressed size 0 -> EOF
        {
            // note: must reload sz_cpr as magic is always stored le32
            sz_cpr = get_le32(&bhdr.sz_cpr);
            if (sz_cpr != UPX_MAGIC_LE32)  // sz_cpr must be h->magic
                throwCompressedDataViolation();
            break;
        }
        // Minimum compressed length: LZMA has 5-byte info header.
        // NRV_d8 has 1-byte initial 8 flag bits, plus end-of-block marker
        // (32 bit look-back offset of all 1s: encoded as 24 pairs of bits
        // {not last, 1} then low 8-bits of 0xff; total: 8 + 2*24 + 8 bits
        // ==> 8 bytes)
        if (sz_unc <= 0 || sz_cpr <= 5u
        ||  sz_cpr > sz_unc || sz_unc > blocksize)
            throwCantUnpack("corrupt b_info %#x %#x", sz_unc, sz_cpr);

        // Compressed output has control bytes such as the 32-bit
        // first flag bits of NRV_d32, the 5-byte info of LZMA, etc.
        // Fuzzers may try sz_cpr shorter than possible.
        // Use some OVERHEAD for safety.
        i = blocksize + OVERHEAD - upx::umax(12u, sz_cpr);
        if (i < 0)
            throwCantUnpack("corrupt b_info %#x %#x", sz_cpr, blocksize);
        fi->readx(buf+i, sz_cpr);
        // update checksum of compressed data (before decrypt for debugging)
        //c_adler = upx_adler32(buf + i, sz_cpr, c_adler);
        // decrypt payload if enabled
        if (dec_use_salt) {
            decrypt_buffer(g_enc_salt, dec_block_index++, buf + i, sz_cpr);
        }
        // update checksum of compressed data (after decrypt)
        c_adler = upx_adler32(buf + i, sz_cpr, c_adler);
        // decompress
        if (sz_cpr < sz_unc) {
            decompress(buf+i, buf, false);
            if (0!=bhdr.b_ftid) {
                Filter ft(ph.level);
                ft.init(bhdr.b_ftid);
                ft.cto = bhdr.b_cto8;
                ft.unfilter(buf, sz_unc);
            }
            i = 0;
        }
        // update checksum of uncompressed data
        u_adler = upx_adler32(buf + i, sz_unc, u_adler);
        total_in  += sz_cpr;
        total_out += sz_unc;
        // write block
        if (fo)
            fo->write(buf + i, sz_unc);
#undef buf
    }

    // update header with totals
    ph.c_len = total_in;
    ph.u_len = total_out;

    // all bytes must be written
    if (ph.version > 8 && total_out != orig_file_size)
        throwEOFException();

    // finally test the checksums
    if (ph.c_adler != c_adler || ph.u_adler != u_adler)
        throwChecksumError();
}

/* vim:set ts=4 sw=4 et: */
