/*******************************************************************\

Module: Read Mach-O

Author:

\*******************************************************************/

#include <cassert>
#include <cstdlib>

#include "osx_fat_reader.h"

#ifdef __APPLE__
#include <mach-o/fat.h>
#endif

/*******************************************************************\

Function: is_osx_fat_magic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_osx_fat_magic(char hdr[4])
{
#ifdef __APPLE__
  uint32_t *magic=reinterpret_cast<uint32_t*>(hdr);

  switch(*magic)
  {
    case FAT_MAGIC:
    case FAT_CIGAM:
      return true;
  }
#endif

  return false;
}

/*******************************************************************\

Function: osx_fat_readert::osx_fat_readert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

osx_fat_readert::osx_fat_readert(std::ifstream &in) :
  has_gb_arch(false)
{
#ifdef __APPLE__
  struct fat_header fh;
  in.read((char*)&fh, sizeof(struct fat_header));

  if(!in)
    throw "failed to read OSX fat header";

  if(!is_osx_fat_magic((char*)&(fh.magic)))
    throw "OSX fat header malformed (magic)";

  assert(sizeof(fh.nfat_arch)==4);
  unsigned narch=__builtin_bswap32(fh.nfat_arch);

  for(unsigned i=0; !has_gb_arch && i<narch; ++i)
  {
    struct fat_arch fa;
    in.read((char*)&fa, sizeof(struct fat_arch));

    assert(sizeof(fa.cputype)==4 &&
           sizeof(fa.cpusubtype)==4 &&
           sizeof(fa.size)==4);
    int cputype=__builtin_bswap32(fa.cputype);
    int cpusubtype=__builtin_bswap32(fa.cpusubtype);
    unsigned size=__builtin_bswap32(fa.size);

    has_gb_arch=cputype==CPU_TYPE_HPPA &&
                cpusubtype==CPU_SUBTYPE_HPPA_7100LC &&
                size > 0;
  }
#endif
}

/*******************************************************************\

Function: osx_fat_readert::extract_gb

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool osx_fat_readert::extract_gb(
  const std::string &source,
  const std::string &dest) const
{
  assert(has_gb_arch);

  std::string command=
    "lipo -thin hppa7100LC -output \""+dest+"\" \""+source+"\"";
  return system(command.c_str())!=0;
}

