/*******************************************************************\

Module: Read Mach-O

Author:

\*******************************************************************/

/// \file
/// Read Mach-O

#include "osx_fat_reader.h"

#include <cstdlib>
#include <util/exception_utils.h>
#include <util/invariant.h>

// we define file-type magic values for all platforms to detect when we find a
// file that we might not be able to process
#define CPROVER_FAT_MAGIC 0xcafebabe
#define CPROVER_FAT_CIGAM 0xbebafeca
#define CPROVER_MH_MAGIC 0xfeedface
#define CPROVER_MH_CIGAM 0xcefaedfe
#define CPROVER_MH_MAGIC_64 0xfeedfacf
#define CPROVER_MH_CIGAM_64 0xcffaedfe

#ifdef __APPLE__
#  include <architecture/byte_order.h>
#  include <mach-o/fat.h>
#  include <mach-o/loader.h>
#  include <mach-o/swap.h>

#  if(CPROVER_FAT_MAGIC != FAT_MAGIC) || (CPROVER_FAT_CIGAM != FAT_CIGAM) ||   \
    (CPROVER_MH_MAGIC != MH_MAGIC) || (CPROVER_MH_CIGAM != MH_CIGAM) ||        \
    (CPROVER_MH_MAGIC_64 != MH_MAGIC_64) ||                                    \
    (CPROVER_MH_CIGAM_64 != MH_CIGAM_64)
#    error "Mach-O magic has inconsistent value"
#  endif
#endif

#include <util/run.h>

struct fat_header_prefixt
{
  uint32_t magic;
  uint32_t n_architectures;
};

static uint32_t u32_to_native_endian(uint32_t input)
{
  const uint8_t *input_as_bytes = reinterpret_cast<uint8_t *>(&input);
  return (((uint32_t)input_as_bytes[0]) << 24) |
         (((uint32_t)input_as_bytes[1]) << 16) |
         (((uint32_t)input_as_bytes[2]) << 8) |
         (((uint32_t)input_as_bytes[3]) << 0);
}

bool is_osx_fat_header(char header_bytes[8])
{
  struct fat_header_prefixt *header =
    reinterpret_cast<struct fat_header_prefixt *>(header_bytes);

  // Unfortunately for us, both Java class files and Mach fat binaries use the
  // magic number 0xCAFEBABE. Therefore we must also check the second field,
  // number of architectures, is in a sensible range (I use at 1 <= archs < 20,
  // the same criterion used by `GNU file`).
  // Luckily the class file format stores the file version here, which cannot
  // fall in this range.
  uint32_t n_architectures_native =
    u32_to_native_endian(header->n_architectures);
  return u32_to_native_endian(header->magic) == CPROVER_FAT_MAGIC &&
         n_architectures_native >= 1 && n_architectures_native < 20;
}

osx_fat_readert::osx_fat_readert(
  std::ifstream &in,
  message_handlert &message_handler)
  : log(message_handler), has_gb_arch(false)
{
#ifdef __APPLE__
  // NOLINTNEXTLINE(readability/identifiers)
  struct fat_header fh;
  // NOLINTNEXTLINE(readability/identifiers)
  in.read(reinterpret_cast<char*>(&fh), sizeof(struct fat_header));

  if(!in)
    throw system_exceptiont("failed to read OSX fat header");

  if(!is_osx_fat_header(reinterpret_cast<char *>(&(fh.magic))))
    throw deserialization_exceptiont("OSX fat header malformed");

  static_assert(
    sizeof(fh.nfat_arch) == 4, "fat_header::nfat_arch is of type uint32_t");
  unsigned narch = u32_to_native_endian(fh.nfat_arch);

  for(unsigned i=0; !has_gb_arch && i<narch; ++i)
  {
    // NOLINTNEXTLINE(readability/identifiers)
    struct fat_arch fa;
    // NOLINTNEXTLINE(readability/identifiers)
    in.read(reinterpret_cast<char*>(&fa), sizeof(struct fat_arch));

    static_assert(
      sizeof(fa.cputype) == 4 && sizeof(fa.cpusubtype) == 4 &&
        sizeof(fa.size) == 4,
      "This requires a specific fat architecture");
    int cputype = u32_to_native_endian(fa.cputype);
    int cpusubtype = u32_to_native_endian(fa.cpusubtype);
    unsigned size = u32_to_native_endian(fa.size);

    has_gb_arch=cputype==CPU_TYPE_HPPA &&
                cpusubtype==CPU_SUBTYPE_HPPA_7100LC &&
                size > 0;
  }
#else
  (void)in;  // unused parameter

  log.warning() << "Cannot read OSX fat archive on this platform"
                << messaget::eom;
#endif
}

bool osx_fat_readert::extract_gb(
  const std::string &source,
  const std::string &dest) const
{
  PRECONDITION(has_gb_arch);

  return run(
           "lipo", {"lipo", "-thin", "hppa7100LC", "-output", dest, source}) !=
         0;
}

// guided by https://lowlevelbits.org/parsing-mach-o-files/
bool is_osx_mach_object(char hdr[4])
{
  uint32_t *magic = reinterpret_cast<uint32_t *>(hdr);

  switch(*magic)
  {
  case CPROVER_MH_MAGIC:
  case CPROVER_MH_CIGAM:
  case CPROVER_MH_MAGIC_64:
  case CPROVER_MH_CIGAM_64:
    return true;
  }

  return false;
}

void osx_mach_o_readert::process_sections_32(uint32_t nsects, bool need_swap)
{
#ifdef __APPLE__
  for(uint32_t i = 0; i < nsects; ++i)
  {
    // NOLINTNEXTLINE(readability/identifiers)
    struct section s;
    in.read(reinterpret_cast<char *>(&s), sizeof(s));

    if(!in)
      throw deserialization_exceptiont("failed to read Mach-O section");

    if(need_swap)
      swap_section(&s, 1, NXHostByteOrder());

    sections.emplace(s.sectname, sectiont(s.sectname, s.offset, s.size));
  }
#else
  // unused parameters
  (void)nsects;
  (void)need_swap;
#endif
}

void osx_mach_o_readert::process_sections_64(uint32_t nsects, bool need_swap)
{
#ifdef __APPLE__
  for(uint32_t i = 0; i < nsects; ++i)
  {
    // NOLINTNEXTLINE(readability/identifiers)
    struct section_64 s;
    in.read(reinterpret_cast<char *>(&s), sizeof(s));

    if(!in)
      throw deserialization_exceptiont("failed to read 64-bit Mach-O section");

    if(need_swap)
      swap_section_64(&s, 1, NXHostByteOrder());

    sections.emplace(s.sectname, sectiont(s.sectname, s.offset, s.size));
  }
#else
  // unused parameters
  (void)nsects;
  (void)need_swap;
#endif
}

void osx_mach_o_readert::process_commands(
  uint32_t ncmds,
  std::size_t offset,
  bool need_swap)
{
#ifdef __APPLE__
  for(uint32_t i = 0; i < ncmds; ++i)
  {
    in.seekg(offset);

    // NOLINTNEXTLINE(readability/identifiers)
    struct load_command lc;
    in.read(reinterpret_cast<char *>(&lc), sizeof(lc));

    if(!in)
      throw deserialization_exceptiont("failed to read Mach-O command");

    if(need_swap)
      swap_load_command(&lc, NXHostByteOrder());

    // we may need to re-read the command once we have figured out its type; in
    // particular, segment commands contain additional information that we have
    // now just read a prefix of
    in.seekg(offset);

    switch(lc.cmd)
    {
    case LC_SEGMENT:
    {
      // NOLINTNEXTLINE(readability/identifiers)
      struct segment_command seg;
      in.read(reinterpret_cast<char *>(&seg), sizeof(seg));

      if(!in)
        throw deserialization_exceptiont("failed to read Mach-O segment");

      if(need_swap)
        swap_segment_command(&seg, NXHostByteOrder());

      process_sections_32(seg.nsects, need_swap);
      break;
    }
    case LC_SEGMENT_64:
    {
      // NOLINTNEXTLINE(readability/identifiers)
      struct segment_command_64 seg;
      in.read(reinterpret_cast<char *>(&seg), sizeof(seg));

      if(!in)
        throw deserialization_exceptiont("failed to read Mach-O segment");

      if(need_swap)
        swap_segment_command_64(&seg, NXHostByteOrder());

      process_sections_64(seg.nsects, need_swap);
      break;
    }
    default:
      break;
    }

    offset += lc.cmdsize;
  }
#else
  // unused parameters
  (void)ncmds;
  (void)offset;
  (void)need_swap;
#endif
}

osx_mach_o_readert::osx_mach_o_readert(
  std::istream &_in,
  message_handlert &message_handler)
  : log(message_handler), in(_in)
{
  // read magic
  uint32_t magic;
  in.read(reinterpret_cast<char *>(&magic), sizeof(magic));

  if(!in)
    throw deserialization_exceptiont("failed to read Mach-O magic");

#ifdef __APPLE__
  bool is_64 = false, need_swap = false;
  switch(magic)
  {
  case CPROVER_MH_CIGAM:
    need_swap = true;
    break;
  case CPROVER_MH_MAGIC:
    break;
  case CPROVER_MH_CIGAM_64:
    need_swap = true;
    is_64 = true;
    break;
  case CPROVER_MH_MAGIC_64:
    is_64 = true;
    break;
  default:
    throw deserialization_exceptiont("no Mach-O magic");
  }

  uint32_t ncmds = 0;
  std::size_t offset = 0;

  // re-read from the beginning, now reading the full header
  in.seekg(0);

  if(!is_64)
  {
    // NOLINTNEXTLINE(readability/identifiers)
    struct mach_header mh;
    in.read(reinterpret_cast<char *>(&mh), sizeof(mh));

    if(!in)
      throw deserialization_exceptiont("failed to read 32-bit Mach-O header");

    if(need_swap)
      swap_mach_header(&mh, NXHostByteOrder());

    ncmds = mh.ncmds;
    offset = sizeof(mh);
  }
  else
  {
    // NOLINTNEXTLINE(readability/identifiers)
    struct mach_header_64 mh;
    in.read(reinterpret_cast<char *>(&mh), sizeof(mh));

    if(!in)
      throw deserialization_exceptiont("failed to read 64-bit Mach-O header");

    if(need_swap)
      swap_mach_header_64(&mh, NXHostByteOrder());

    ncmds = mh.ncmds;
    offset = sizeof(mh);
  }

  process_commands(ncmds, offset, need_swap);
#else
  log.warning() << "Cannot read OSX Mach-O on this platform" << messaget::eom;
#endif
}
