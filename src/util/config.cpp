/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "config.h"

#include <cstdlib>

#include "arith_tools.h"
#include "cmdline.h"
#include "cprover_prefix.h"
#include "exception_utils.h"
#include "namespace.h"
#include "simplify_expr.h"
#include "std_expr.h"
#include "string2int.h"
#include "string_utils.h"
#include "symbol_table.h"

configt config;

void configt::ansi_ct::set_16()
{
  set_LP32();
}

void configt::ansi_ct::set_32()
{
  set_ILP32();
}

void configt::ansi_ct::set_64()
{
  #ifdef _WIN32
  set_LLP64();
  #else
  set_LP64();
  #endif
}

/// int=32, long=64, pointer=64
void configt::ansi_ct::set_LP64()
{
  bool_width=1*8;
  int_width=4*8;
  long_int_width=8*8;
  char_width=1*8;
  short_int_width=2*8;
  long_long_int_width=8*8;
  pointer_width=8*8;
  single_width=4*8;
  double_width=8*8;
  long_double_width=16*8;
  char_is_unsigned=false;
  wchar_t_is_unsigned=false;
  wchar_t_width=4*8;
  alignment=1;
  memory_operand_size=int_width/8;
}

/// int=64, long=64, pointer=64
// TODO: find the alignment restrictions (per type) of the different
// architectures (currently: sizeof=alignedof)
// TODO: implement the __attribute__((__aligned__(val)))

void configt::ansi_ct::set_ILP64()
{
  bool_width=1*8;
  int_width=8*8;
  long_int_width=8*8;
  char_width=1*8;
  short_int_width=2*8;
  long_long_int_width=8*8;
  pointer_width=8*8;
  single_width=4*8;
  double_width=8*8;
  long_double_width=8*8;
  char_is_unsigned=false;
  wchar_t_is_unsigned=false;
  wchar_t_width=4*8;
  alignment=1;
  memory_operand_size=int_width/8;
}

/// int=32, long=32, pointer=64
void configt::ansi_ct::set_LLP64()
{
  bool_width=1*8;
  int_width=4*8;
  long_int_width=4*8;
  char_width=1*8;
  short_int_width=2*8;
  long_long_int_width=8*8;
  pointer_width=8*8;
  single_width=4*8;
  double_width=8*8;
  long_double_width=8*8;
  char_is_unsigned=false;
  wchar_t_is_unsigned=false;
  wchar_t_width=4*8;
  alignment=1;
  memory_operand_size=int_width/8;
}

/// int=32, long=32, pointer=32
void configt::ansi_ct::set_ILP32()
{
  bool_width=1*8;
  int_width=4*8;
  long_int_width=4*8;
  char_width=1*8;
  short_int_width=2*8;
  long_long_int_width=8*8;
  pointer_width=4*8;
  single_width=4*8;
  double_width=8*8;
  long_double_width=12*8; // really 96 bits on GCC
  char_is_unsigned=false;
  wchar_t_is_unsigned=false;
  wchar_t_width=4*8;
  alignment=1;
  memory_operand_size=int_width/8;
}

/// int=16, long=32, pointer=32
void configt::ansi_ct::set_LP32()
{
  bool_width=1*8;
  int_width=2*8;
  long_int_width=4*8;
  char_width=1*8;
  short_int_width=2*8;
  long_long_int_width=8*8;
  pointer_width=4*8;
  single_width=4*8;
  double_width=8*8;
  long_double_width=8*8;
  char_is_unsigned=false;
  wchar_t_is_unsigned=false;
  wchar_t_width=4*8;
  alignment=1;
  memory_operand_size=int_width/8;
}

void configt::ansi_ct::set_arch_spec_i386()
{
  set_ILP32();
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
  case flavourt::CLANG:
    defines.push_back("i386");
    defines.push_back("__i386");
    defines.push_back("__i386__");
    if(mode == flavourt::CLANG)
      defines.push_back("__LITTLE_ENDIAN__");
    break;

  case flavourt::VISUAL_STUDIO:
    defines.push_back("_M_IX86");
    break;

  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_x86_64()
{
  set_LP64();
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  long_double_width=16*8;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
  case flavourt::CLANG:
    defines.push_back("__LP64__");
    defines.push_back("__x86_64");
    defines.push_back("__x86_64__");
    defines.push_back("_LP64");
    defines.push_back("__amd64__");
    defines.push_back("__amd64");

    if(os == ost::OS_MACOS)
      defines.push_back("__LITTLE_ENDIAN__");
    break;

  case flavourt::VISUAL_STUDIO:
    defines.push_back("_M_X64");
    defines.push_back("_M_AMD64");
    break;

  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_power(const irep_idt &subarch)
{
  if(subarch=="powerpc")
    set_ILP32();
  else // ppc64 or ppc64le
    set_LP64();

  if(subarch=="ppc64le")
    endianness=endiannesst::IS_LITTLE_ENDIAN;
  else
    endianness=endiannesst::IS_BIG_ENDIAN;

  long_double_width=16*8;
  char_is_unsigned=true;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
  case flavourt::CLANG:
    defines.push_back("__powerpc");
    defines.push_back("__powerpc__");
    defines.push_back("__POWERPC__");
    defines.push_back("__ppc__");

    if(os == ost::OS_MACOS)
      defines.push_back("__BIG_ENDIAN__");

    if(subarch!="powerpc")
    {
      defines.push_back("__powerpc64");
      defines.push_back("__powerpc64__");
      defines.push_back("__PPC64__");
      defines.push_back("__ppc64__");
      if(subarch=="ppc64le")
      {
        defines.push_back("_CALL_ELF=2");
        defines.push_back("__LITTLE_ENDIAN__");
      }
      else
      {
        defines.push_back("_CALL_ELF=1");
        defines.push_back("__BIG_ENDIAN__");
      }
    }
    break;

  case flavourt::VISUAL_STUDIO:
    defines.push_back("_M_PPC");
    break;

  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_arm(const irep_idt &subarch)
{
  if(subarch=="arm64")
  {
    set_LP64();
    long_double_width=16*8;
  }
  else
  {
    set_ILP32();
    long_double_width=8*8;
  }

  endianness=endiannesst::IS_LITTLE_ENDIAN;
  char_is_unsigned=true;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
  case flavourt::CLANG:
    if(subarch=="arm64")
      defines.push_back("__aarch64__");
    else
      defines.push_back("__arm__");
    if(subarch=="armhf")
      defines.push_back("__ARM_PCS_VFP");
    break;

  case flavourt::VISUAL_STUDIO:
    defines.push_back("_M_ARM");
    break;

  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_alpha()
{
  set_LP64();
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  long_double_width=16*8;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__alpha__");
    break;

  case flavourt::VISUAL_STUDIO:
    defines.push_back("_M_ALPHA");
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_mips(const irep_idt &subarch)
{
  if(subarch=="mipsel" ||
     subarch=="mips" ||
     subarch=="mipsn32el" ||
     subarch=="mipsn32")
  {
    set_ILP32();
    long_double_width=8*8;
  }
  else
  {
    set_LP64();
    long_double_width=16*8;
  }

  if(subarch=="mipsel" ||
     subarch=="mipsn32el" ||
     subarch=="mips64el")
    endianness=endiannesst::IS_LITTLE_ENDIAN;
  else
    endianness=endiannesst::IS_BIG_ENDIAN;

  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__mips__");
    defines.push_back("mips");
    defines.push_back(
      "_MIPS_SZPTR="+std::to_string(config.ansi_c.pointer_width));
    break;

  case flavourt::VISUAL_STUDIO:
    UNREACHABLE; // not supported by Visual Studio
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_riscv64()
{
  set_LP64();
  endianness = endiannesst::IS_LITTLE_ENDIAN;
  long_double_width = 16 * 8;
  char_is_unsigned = true;
  NULL_is_zero = true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__riscv");
    break;

  case flavourt::VISUAL_STUDIO:
  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_s390()
{
  set_ILP32();
  endianness=endiannesst::IS_BIG_ENDIAN;
  long_double_width=16*8;
  char_is_unsigned=true;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__s390__");
    break;

  case flavourt::VISUAL_STUDIO:
    UNREACHABLE; // not supported by Visual Studio
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_s390x()
{
  set_LP64();
  endianness=endiannesst::IS_BIG_ENDIAN;
  char_is_unsigned=true;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__s390x__");
    break;

  case flavourt::VISUAL_STUDIO:
    UNREACHABLE; // not supported by Visual Studio
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_sparc(const irep_idt &subarch)
{
  if(subarch=="sparc64")
  {
    set_LP64();
    long_double_width=16*8;
  }
  else
  {
    set_ILP32();
    long_double_width=16*8;
  }

  endianness=endiannesst::IS_BIG_ENDIAN;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__sparc__");
    if(subarch=="sparc64")
      defines.push_back("__arch64__");
    break;

  case flavourt::VISUAL_STUDIO:
    UNREACHABLE; // not supported by Visual Studio
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_ia64()
{
  set_LP64();
  long_double_width=16*8;
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__ia64__");
    defines.push_back("_IA64");
    defines.push_back("__IA64__");
    break;

  case flavourt::VISUAL_STUDIO:
    defines.push_back("_M_IA64");
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_x32()
{
  // This is a variant of x86_64 that has
  // 32-bit long int and 32-bit pointers.
  set_ILP32();
  long_double_width=16*8; // different from i386
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__ILP32__");
    defines.push_back("__x86_64");
    defines.push_back("__x86_64__");
    defines.push_back("__amd64__");
    defines.push_back("__amd64");
    break;

  case flavourt::VISUAL_STUDIO:
    UNREACHABLE; // not supported by Visual Studio
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

/// Sets up the widths of variables for the Renesas V850
/// \return None
void configt::ansi_ct::set_arch_spec_v850()
{
  // The Renesas V850 is a 32-bit microprocessor used in
  // many automotive applications.  This spec is written from the
  // architecture manual rather than having access to a running
  // system.  Thus some assumptions have been made.

  set_ILP32();

  // Technically, the V850's don't have floating-point at all.
  // However, the RH850, aimed at automotive has both 32-bit and
  // 64-bit IEEE-754 float.
  double_width=8*8;
  long_double_width=8*8;
  endianness=endiannesst::IS_LITTLE_ENDIAN;

  // Without information about the compiler and RTOS, these are guesses
  char_is_unsigned=false;
  NULL_is_zero=true;

  // No preprocessor definitions due to lack of information
}

void configt::ansi_ct::set_arch_spec_hppa()
{
  set_ILP32();
  long_double_width=8*8; // different from i386
  endianness=endiannesst::IS_BIG_ENDIAN;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__hppa__");
    break;

  case flavourt::VISUAL_STUDIO:
    UNREACHABLE; // not supported by Visual Studio
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

void configt::ansi_ct::set_arch_spec_sh4()
{
  set_ILP32();
  long_double_width=8*8; // different from i386
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::GCC:
    defines.push_back("__sh__");
    defines.push_back("__SH4__");
    break;

  case flavourt::VISUAL_STUDIO:
    UNREACHABLE; // not supported by Visual Studio
    break;

  case flavourt::CLANG:
  case flavourt::CODEWARRIOR:
  case flavourt::ARM:
  case flavourt::ANSI:
    break;

  case flavourt::NONE:
    UNREACHABLE;
  }
}

configt::ansi_ct::c_standardt configt::ansi_ct::default_c_standard()
{
  #if defined(__APPLE__)
  // By default, clang on the Mac builds C code in GNU C11
  return c_standardt::C11;
  #elif defined(__FreeBSD__)
  // By default, clang on FreeBSD builds C code in GNU C99
  return c_standardt::C99;
  #else
  // By default, gcc 5.4 or higher use gnu11; older versions use gnu89
  return c_standardt::C11;
  #endif
}

configt::cppt::cpp_standardt configt::cppt::default_cpp_standard()
{
  // g++ 6.3 uses gnu++14
  // g++ 5.4 uses gnu++98
  // clang 6.0 uses c++14
  #if defined _WIN32
  return cpp_standardt::CPP14;
  #else
  return cpp_standardt::CPP98;
  #endif
}

void configt::set_arch(const irep_idt &arch)
{
  ansi_c.arch=arch;

  if(arch=="none")
  {
    // the architecture for people who can't commit
    ansi_c.endianness=configt::ansi_ct::endiannesst::NO_ENDIANNESS;
    ansi_c.lib=configt::ansi_ct::libt::LIB_NONE;
    ansi_c.NULL_is_zero=false;

    if(sizeof(long int)==8)
      ansi_c.set_64();
    else
      ansi_c.set_32();
  }
  else if(arch=="alpha")
    ansi_c.set_arch_spec_alpha();
  else if(arch=="arm64" ||
          arch=="armel" ||
          arch=="armhf" ||
          arch=="arm")
    ansi_c.set_arch_spec_arm(arch);
  else if(arch=="mips64el" ||
          arch=="mipsn32el" ||
          arch=="mipsel" ||
          arch=="mips64" ||
          arch=="mipsn32" ||
          arch=="mips")
    ansi_c.set_arch_spec_mips(arch);
  else if(arch=="powerpc" ||
          arch=="ppc64" ||
          arch=="ppc64le")
    ansi_c.set_arch_spec_power(arch);
  else if(arch == "riscv64")
    ansi_c.set_arch_spec_riscv64();
  else if(arch=="sparc" ||
          arch=="sparc64")
    ansi_c.set_arch_spec_sparc(arch);
  else if(arch=="ia64")
    ansi_c.set_arch_spec_ia64();
  else if(arch=="s390x")
    ansi_c.set_arch_spec_s390x();
  else if(arch=="s390")
    ansi_c.set_arch_spec_s390();
  else if(arch=="x32")
    ansi_c.set_arch_spec_x32();
  else if(arch=="v850")
    ansi_c.set_arch_spec_v850();
  else if(arch=="hppa")
    ansi_c.set_arch_spec_hppa();
  else if(arch=="sh4")
    ansi_c.set_arch_spec_sh4();
  else if(arch=="x86_64")
    ansi_c.set_arch_spec_x86_64();
  else if(arch=="i386")
    ansi_c.set_arch_spec_i386();
  else
  {
    // We run on something new and unknown.
    // We verify for i386 instead.
    ansi_c.set_arch_spec_i386();
    ansi_c.arch="i386";
  }
}

bool configt::set(const cmdlinet &cmdline)
{
  // defaults -- we match the architecture we have ourselves

  cpp.cpp_standard=cppt::default_cpp_standard();

  bv_encoding.object_bits=bv_encoding.default_object_bits;
  // This will allow us to override by language defaults later.
  bv_encoding.is_object_bits_default=true;

  ansi_c.single_precision_constant=false;
  ansi_c.for_has_scope=true; // C99 or later
  ansi_c.ts_18661_3_Floatn_types=false;
  ansi_c.c_standard=ansi_ct::default_c_standard();
  ansi_c.endianness=ansi_ct::endiannesst::NO_ENDIANNESS;
  ansi_c.os=ansi_ct::ost::NO_OS;
  ansi_c.arch="none";
  ansi_c.lib=configt::ansi_ct::libt::LIB_NONE;
  // NOLINTNEXTLINE(readability/casting)
  ansi_c.NULL_is_zero=reinterpret_cast<size_t>(nullptr)==0;

  // Default is ROUND_TO_EVEN, justified by C99:
  // 1 At program startup the floating-point environment is initialized as
  // prescribed by IEC 60559:
  // - All floating-point exception status flags are cleared.
  // - The rounding direction mode is rounding to nearest.
  ansi_c.rounding_mode=ieee_floatt::ROUND_TO_EVEN;

  if(cmdline.isset("function"))
    main=cmdline.get_value("function");

  if(cmdline.isset('D'))
    ansi_c.defines=cmdline.get_values('D');

  if(cmdline.isset('I'))
    ansi_c.include_paths=cmdline.get_values('I');

  if(cmdline.isset("classpath"))
  {
    // Specifying -classpath or -cp overrides any setting of the
    // CLASSPATH environment variable.
    set_classpath(cmdline.get_value("classpath"));
  }
  else if(cmdline.isset("cp"))
  {
    // Specifying -classpath or -cp overrides any setting of the
    // CLASSPATH environment variable.
    set_classpath(cmdline.get_value("cp"));
  }
  else
  {
    // environment variable set?
    const char *CLASSPATH=getenv("CLASSPATH");
    if(CLASSPATH!=nullptr)
      set_classpath(CLASSPATH);
    else
      set_classpath("."); // default
  }

  if(cmdline.isset("main-class"))
    java.main_class=cmdline.get_value("main-class");

  if(cmdline.isset("include"))
    ansi_c.include_files=cmdline.get_values("include");

  // the default architecture is the one we run on
  irep_idt this_arch=this_architecture();
  irep_idt arch=this_arch;

  // let's pick an OS now
  // the default is the one we run on
  irep_idt this_os=this_operating_system();
  irep_idt os=this_os;

  if(cmdline.isset("i386-linux"))
  {
    os="linux";
    arch="i386";
  }
  else if(cmdline.isset("i386-win32") ||
          cmdline.isset("win32"))
  {
    os="windows";
    arch="i386";
  }
  else if(cmdline.isset("winx64"))
  {
    os="windows";
    arch="x86_64";
  }
  else if(cmdline.isset("i386-macos"))
  {
    os="macos";
    arch="i386";
  }
  else if(cmdline.isset("ppc-macos"))
  {
    arch="powerpc";
    os="macos";
  }

  if(cmdline.isset("arch"))
  {
    arch=cmdline.get_value("arch");
  }

  if(cmdline.isset("os"))
  {
    os=cmdline.get_value("os");
  }

  if(os=="windows")
  {
    // Cygwin uses GCC throughout, use i386-linux
    // MinGW needs --win32 --gcc
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_WIN;

    if(cmdline.isset("gcc"))
    {
      // There are gcc versions that target Windows (MinGW for example),
      // and we support that.
      ansi_c.preprocessor=ansi_ct::preprocessort::GCC;
      ansi_c.mode=ansi_ct::flavourt::GCC;

      // enable Cygwin
      #ifdef _WIN32
      ansi_c.defines.push_back("__CYGWIN__");
      #endif

      // MinGW has extra defines
      ansi_c.defines.push_back("__int64=long long");
    }
    else
    {
      // On Windows, our default is Visual Studio.
      // On FreeBSD, it's clang.
      // On anything else, it's GCC as the preprocessor,
      // but we recognize the Visual Studio language,
      // which is somewhat inconsistent.
      #ifdef _WIN32
      ansi_c.preprocessor=ansi_ct::preprocessort::VISUAL_STUDIO;
      ansi_c.mode=ansi_ct::flavourt::VISUAL_STUDIO;
      #elif __FreeBSD__
      ansi_c.preprocessor=ansi_ct::preprocessort::CLANG;
      ansi_c.mode=ansi_ct::flavourt::VISUAL_STUDIO;
      #else
      ansi_c.preprocessor=ansi_ct::preprocessort::GCC;
      ansi_c.mode=ansi_ct::flavourt::VISUAL_STUDIO;
      #endif
    }
  }
  else if(os=="macos")
  {
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_MACOS;
    ansi_c.mode = ansi_ct::flavourt::CLANG;
    ansi_c.preprocessor=ansi_ct::preprocessort::CLANG;
  }
  else if(os=="linux" || os=="solaris")
  {
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_LINUX;
    ansi_c.mode=ansi_ct::flavourt::GCC;
    ansi_c.preprocessor=ansi_ct::preprocessort::GCC;
  }
  else if(os=="freebsd")
  {
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_LINUX;
    ansi_c.mode=ansi_ct::flavourt::CLANG;
    ansi_c.preprocessor=ansi_ct::preprocessort::CLANG;
  }
  else
  {
    // give up, but use reasonable defaults
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_LINUX;
    ansi_c.mode=ansi_ct::flavourt::GCC;
    ansi_c.preprocessor=ansi_ct::preprocessort::GCC;
  }

  if(ansi_c.preprocessor == ansi_ct::preprocessort::GCC)
    ansi_c.Float128_type = true;

  set_arch(arch);

  if(os=="windows")
  {
    // note that sizeof(void *)==8, but sizeof(long)==4!
    if(arch=="x86_64")
      ansi_c.set_LLP64();

    // On Windows, wchar_t is unsigned 16 bit, regardless
    // of the compiler used.
    ansi_c.wchar_t_width=2*8;
    ansi_c.wchar_t_is_unsigned=true;

    // long double is the same as double in Visual Studio,
    // but it's 16 bytes with GCC with the 64-bit target.
    if(arch=="x64_64" && cmdline.isset("gcc"))
      ansi_c.long_double_width=16*8;
    else
      ansi_c.long_double_width=8*8;
  }

  // Let's check some of the type widths in case we run
  // the same architecture and OS that we are verifying for.
  if(arch==this_arch && os==this_os)
  {
    INVARIANT(
      ansi_c.int_width == sizeof(int) * 8,
      "int width shall be equal to the system int width");
    INVARIANT(
      ansi_c.long_int_width == sizeof(long) * 8,
      "long int width shall be equal to the system long int width");
    INVARIANT(
      ansi_c.bool_width == sizeof(bool) * 8,
      "bool width shall be equal to the system bool width");
    INVARIANT(
      ansi_c.char_width == sizeof(char) * 8,
      "char width shall be equal to the system char width");
    INVARIANT(
      ansi_c.short_int_width == sizeof(short) * 8,
      "short int width shall be equal to the system short int width");
    INVARIANT(
      ansi_c.long_long_int_width == sizeof(long long) * 8,
      "long long int width shall be equal to the system long long int width");
    INVARIANT(
      ansi_c.pointer_width == sizeof(void *) * 8,
      "pointer width shall be equal to the system pointer width");
    INVARIANT(
      ansi_c.single_width == sizeof(float) * 8,
      "float width shall be equal to the system float width");
    INVARIANT(
      ansi_c.double_width == sizeof(double) * 8,
      "double width shall be equal to the system double width");
    INVARIANT(
      ansi_c.char_is_unsigned == (static_cast<char>(255) == 255),
      "char_is_unsigned flag shall indicate system char unsignedness");

    #ifndef _WIN32
    // On Windows, long double width varies by compiler
    INVARIANT(
      ansi_c.long_double_width == sizeof(long double) * 8,
      "long double width shall be equal to the system long double width");
    #endif
  }

  // the following allows overriding the defaults

  if(cmdline.isset("16"))
    ansi_c.set_16();

  if(cmdline.isset("32"))
    ansi_c.set_32();

  if(cmdline.isset("64"))
    ansi_c.set_64();

  if(cmdline.isset("LP64"))
    ansi_c.set_LP64();  // int=32, long=64, pointer=64

  if(cmdline.isset("ILP64"))
    ansi_c.set_ILP64(); // int=64, long=64, pointer=64

  if(cmdline.isset("LLP64"))
    ansi_c.set_LLP64(); // int=32, long=32, pointer=64

  if(cmdline.isset("ILP32"))
    ansi_c.set_ILP32(); // int=32, long=32, pointer=32

  if(cmdline.isset("LP32"))
    ansi_c.set_LP32();  // int=16, long=32, pointer=32

  if(cmdline.isset("string-abstraction"))
    ansi_c.string_abstraction=true;
  else
    ansi_c.string_abstraction=false;

  if(cmdline.isset("no-library"))
    ansi_c.lib=configt::ansi_ct::libt::LIB_NONE;

  if(cmdline.isset("little-endian"))
    ansi_c.endianness=configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;

  if(cmdline.isset("big-endian"))
    ansi_c.endianness=configt::ansi_ct::endiannesst::IS_BIG_ENDIAN;

  if(cmdline.isset("little-endian") &&
     cmdline.isset("big-endian"))
    return true;

  if(cmdline.isset("unsigned-char"))
    ansi_c.char_is_unsigned=true;

  if(cmdline.isset("round-to-even") ||
     cmdline.isset("round-to-nearest"))
    ansi_c.rounding_mode=ieee_floatt::ROUND_TO_EVEN;

  if(cmdline.isset("round-to-plus-inf"))
    ansi_c.rounding_mode=ieee_floatt::ROUND_TO_PLUS_INF;

  if(cmdline.isset("round-to-minus-inf"))
    ansi_c.rounding_mode=ieee_floatt::ROUND_TO_MINUS_INF;

  if(cmdline.isset("round-to-zero"))
    ansi_c.rounding_mode=ieee_floatt::ROUND_TO_ZERO;

  if(cmdline.isset("object-bits"))
  {
    bv_encoding.object_bits=
      unsafe_string2unsigned(cmdline.get_value("object-bits"));

    if(!(0<bv_encoding.object_bits &&
         bv_encoding.object_bits<ansi_c.pointer_width))
    {
      throw invalid_command_line_argument_exceptiont(
        "object-bits must be positive and less than the pointer width (" +
          std::to_string(ansi_c.pointer_width) + ") ",
        "--object_bits");
    }

    bv_encoding.is_object_bits_default = false;
  }

  return false;
}

std::string configt::ansi_ct::os_to_string(ost os)
{
  switch(os)
  {
  case ost::OS_LINUX: return "linux";
  case ost::OS_MACOS: return "macos";
  case ost::OS_WIN: return "win";
  default: return "none";
  }

  UNREACHABLE;
}

configt::ansi_ct::ost configt::ansi_ct::string_to_os(const std::string &os)
{
  if(os=="linux")
    return ost::OS_LINUX;
  else if(os=="macos")
    return ost::OS_MACOS;
  else if(os=="win")
    return ost::OS_WIN;
  else
    return ost::NO_OS;
}

static irep_idt string_from_ns(
  const namespacet &ns,
  const std::string &what)
{
  const irep_idt id=CPROVER_PREFIX "architecture_"+what;
  const symbolt *symbol;

  const bool not_found = ns.lookup(id, symbol);
  INVARIANT(!not_found, id2string(id) + " must be in namespace");

  const exprt &tmp=symbol->value;

  INVARIANT(
    tmp.id() == ID_address_of &&
      to_address_of_expr(tmp).object().id() == ID_index &&
      to_index_expr(to_address_of_expr(tmp).object()).array().id() ==
        ID_string_constant,
    "symbol table configuration entry `" + id2string(id) +
      "' must be a string constant");

  return to_index_expr(to_address_of_expr(tmp).object()).array().get(ID_value);
}

static unsigned unsigned_from_ns(
  const namespacet &ns,
  const std::string &what)
{
  const irep_idt id=CPROVER_PREFIX "architecture_"+what;
  const symbolt *symbol;

  const bool not_found = ns.lookup(id, symbol);
  INVARIANT(!not_found, id2string(id) + " must be in namespace");

  exprt tmp=symbol->value;
  simplify(tmp, ns);

  INVARIANT(
    tmp.id() == ID_constant,
    "symbol table configuration entry `" + id2string(id) +
      "' must be a constant");

  mp_integer int_value;

  const bool error = to_integer(to_constant_expr(tmp), int_value);
  INVARIANT(
    !error,
    "symbol table configuration entry `" + id2string(id) +
      "' must be convertible to mp_integer");

  return numeric_cast_v<unsigned>(int_value);
}

void configt::set_from_symbol_table(
  const symbol_tablet &symbol_table)
{
  // maybe not compiled from C/C++
  if(symbol_table.symbols.find(CPROVER_PREFIX "architecture_" "int_width")==
     symbol_table.symbols.end())
    return;

  namespacet ns(symbol_table);

  // clear defines
  ansi_c.defines.clear();

  // first set architecture to get some defaults
  if(symbol_table.symbols.find(CPROVER_PREFIX "architecture_" "arch")==
     symbol_table.symbols.end())
    set_arch(id2string(this_architecture()));
  else
    set_arch(string_from_ns(ns, "arch"));

  ansi_c.int_width=unsigned_from_ns(ns, "int_width");
  ansi_c.long_int_width=unsigned_from_ns(ns, "long_int_width");
  ansi_c.bool_width=1*8;
  ansi_c.char_width=unsigned_from_ns(ns, "char_width");
  ansi_c.short_int_width=unsigned_from_ns(ns, "short_int_width");
  ansi_c.long_long_int_width=unsigned_from_ns(ns, "long_long_int_width");
  ansi_c.pointer_width=unsigned_from_ns(ns, "pointer_width");
  ansi_c.single_width=unsigned_from_ns(ns, "single_width");
  ansi_c.double_width=unsigned_from_ns(ns, "double_width");
  ansi_c.long_double_width=unsigned_from_ns(ns, "long_double_width");
  ansi_c.wchar_t_width=unsigned_from_ns(ns, "wchar_t_width");

  ansi_c.char_is_unsigned=unsigned_from_ns(ns, "char_is_unsigned")!=0;
  ansi_c.wchar_t_is_unsigned=unsigned_from_ns(ns, "wchar_t_is_unsigned")!=0;
  // for_has_scope, single_precision_constant, rounding_mode,
  // ts_18661_3_Floatn_types are not architectural features,
  // and thus not stored in namespace

  ansi_c.alignment=unsigned_from_ns(ns, "alignment");

  ansi_c.memory_operand_size=unsigned_from_ns(ns, "memory_operand_size");

  ansi_c.endianness=(ansi_ct::endiannesst)unsigned_from_ns(ns, "endianness");

  if(symbol_table.symbols.find(CPROVER_PREFIX "architecture_" "os")==
     symbol_table.symbols.end())
    ansi_c.os=ansi_ct::string_to_os(id2string(this_operating_system()));
  else
    ansi_c.os=ansi_ct::string_to_os(id2string(string_from_ns(ns, "os")));

  // NULL_is_zero=from_ns("NULL_is_zero");
  ansi_c.NULL_is_zero=true;

  // mode, preprocessor (and all preprocessor command line options),
  // lib, string_abstraction not stored in namespace

  set_object_bits_from_symbol_table(symbol_table);
}

/// Sets the number of bits used for object addresses
/// \param symbol_table: The symbol table
void configt::set_object_bits_from_symbol_table(
  const symbol_tablet &symbol_table)
{
  // has been overridden by command line option,
  //   thus do not apply language defaults
  if(!bv_encoding.is_object_bits_default)
    return;

  // set object_bits according to entry point language
  if(const auto maybe_symbol=symbol_table.lookup(CPROVER_PREFIX "_start"))
  {
    const symbolt &entry_point_symbol=*maybe_symbol;

    if(entry_point_symbol.mode==ID_java)
      bv_encoding.object_bits=java.default_object_bits;
    else if(entry_point_symbol.mode==ID_C)
      bv_encoding.object_bits=ansi_c.default_object_bits;
    else if(entry_point_symbol.mode==ID_cpp)
      bv_encoding.object_bits=cpp.default_object_bits;
    DATA_INVARIANT(
      0<bv_encoding.object_bits && bv_encoding.object_bits<ansi_c.pointer_width,
      "object_bits should fit into pointer width");
  }
}

std::string configt::object_bits_info()
{
  return "Running with "+std::to_string(bv_encoding.object_bits)+
    " object bits, "+
    std::to_string(ansi_c.pointer_width-bv_encoding.object_bits)+
    " offset bits ("+
    (bv_encoding.is_object_bits_default ? "default" : "user-specified")+
    ")";
}

// clang-format off
irep_idt configt::this_architecture()
{
  irep_idt this_arch;

  // following http://wiki.debian.org/ArchitectureSpecificsMemo

  #ifdef __alpha__
  this_arch = "alpha";
  #elif defined(__armel__)
  this_arch = "armel";
  #elif defined(__aarch64__)
  this_arch = "arm64";
  #elif defined(__arm__)
    #ifdef __ARM_PCS_VFP
    this_arch = "armhf"; // variant of arm with hard float
    #else
    this_arch = "arm";
    #endif
  #elif defined(__mipsel__)
    #if _MIPS_SIM==_ABIO32
    this_arch = "mipsel";
    #elif _MIPS_SIM==_ABIN32
    this_arch = "mipsn32el";
    #else
    this_arch = "mips64el";
    #endif
  #elif defined(__mips__)
    #if _MIPS_SIM==_ABIO32
    this_arch = "mips";
    #elif _MIPS_SIM==_ABIN32
    this_arch = "mipsn32";
    #else
    this_arch = "mips64";
    #endif
  #elif defined(__powerpc__)
    #if defined(__ppc64__) || defined(__PPC64__) || \
        defined(__powerpc64__) || defined(__POWERPC64__)
      #ifdef __LITTLE_ENDIAN__
      this_arch = "ppc64le";
      #else
      this_arch = "ppc64";
      #endif
    #else
    this_arch = "powerpc";
    #endif
  #elif defined(__riscv)
    this_arch = "riscv64";
  #elif defined(__sparc__)
    #ifdef __arch64__
      this_arch = "sparc64";
    #else
      this_arch = "sparc";
    #endif
  #elif defined(__ia64__)
    this_arch = "ia64";
  #elif defined(__s390x__)
    this_arch = "s390x";
  #elif defined(__s390__)
    this_arch = "s390";
  #elif defined(__x86_64__)
    #ifdef __ILP32__
      this_arch = "x32"; // variant of x86_64 with 32-bit pointers
    #else
      this_arch = "x86_64";
    #endif
  #elif defined(__i386__)
    this_arch = "i386";
  #elif defined(_WIN64)
    this_arch = "x86_64";
  #elif defined(_WIN32)
    this_arch = "i386";
  #elif defined(__hppa__)
    this_arch = "hppa";
  #elif defined(__sh__)
    this_arch = "sh4";
  #else
    // something new and unknown!
    this_arch = "unknown";
  #endif

  return this_arch;
}
// clang-format on

void configt::set_classpath(const std::string &cp)
{
// These are separated by colons on Unix, and semicolons on
// Windows.
#ifdef _WIN32
  const char cp_separator = ';';
#else
  const char cp_separator = ':';
#endif

  std::vector<std::string> class_path =
    split_string(cp, cp_separator);
  java.classpath.insert(
    java.classpath.end(), class_path.begin(), class_path.end());
}

irep_idt configt::this_operating_system()
{
  irep_idt this_os;

  #ifdef _WIN32
  this_os="windows";
  #elif __APPLE__
  this_os="macos";
  #elif __FreeBSD__
  this_os="freebsd";
  #elif __linux__
  this_os="linux";
  #elif __SVR4
  this_os="solaris";
  #else
  this_os="unknown";
  #endif

  return this_os;
}
