/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include "namespace.h"
#include "config.h"
#include "symbol_table.h"
#include "arith_tools.h"
#include "cmdline.h"
#include "simplify_expr.h"
#include "i2string.h"
#include "std_expr.h"
#include "cprover_prefix.h"

configt config;

/*******************************************************************\

Function: configt::ansi_ct::set_16

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_16()
{
  set_LP32();
}

/*******************************************************************\

Function: configt::ansi_ct::set_32

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_32()
{
  set_ILP32();
}

/*******************************************************************\

Function: configt::ansi_ct::set_64

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_64()
{
  #ifdef _WIN32
  set_LLP64();
  #else
  set_LP64();
  #endif
}

/*******************************************************************\

Function: configt::ansi_ct::set_LP64

  Inputs:

 Outputs:

 Purpose: int=32, long=64, pointer=64

\*******************************************************************/

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

/*******************************************************************\

Function: configt::ansi_ct::set_ILP64

  Inputs:

 Outputs:

 Purpose: int=64, long=64, pointer=64

\*******************************************************************/

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

/*******************************************************************\

Function: configt::ansi_ct::set_LLP64

  Inputs:

 Outputs:

 Purpose: int=32, long=32, pointer=64

\*******************************************************************/

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

/*******************************************************************\

Function: configt::ansi_ct::set_ILP32

  Inputs:

 Outputs:

 Purpose: int=32, long=32, pointer=32

\*******************************************************************/

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

/*******************************************************************\

Function: configt::ansi_ct::set_LP32

  Inputs:

 Outputs:

 Purpose: int=16, long=32, pointer=32

\*******************************************************************/

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

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_i386

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_arch_spec_i386()
{
  set_ILP32();
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("i386");
    defines.push_back("__i386");
    defines.push_back("__i386__");
    if(os==ost::OS_MACOS)
      defines.push_back("__LITTLE_ENDIAN__");
    break;

  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    defines.push_back("_M_IX86");
    break;

  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;

  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_x86_64

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_arch_spec_x86_64()
{
  set_LP64();
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  long_double_width=16*8;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__LP64__");
    defines.push_back("__x86_64");
    defines.push_back("__x86_64__");
    defines.push_back("_LP64");
    defines.push_back("__amd64__");
    defines.push_back("__amd64");
    if(os==ost::OS_MACOS)
      defines.push_back("__LITTLE_ENDIAN__");
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    defines.push_back("_M_X64");
    defines.push_back("_M_AMD64");
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_power

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__powerpc");
    defines.push_back("__powerpc__");
    defines.push_back("__POWERPC__");
    defines.push_back("__ppc__");

    if(os==ost::OS_MACOS)
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

  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    defines.push_back("_M_PPC");
    break;

  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;

  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_arm

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    if(subarch=="arm64")
      defines.push_back("__aarch64__");
    else
      defines.push_back("__arm__");
    if(subarch=="armhf")
      defines.push_back("__ARM_PCS_VFP");
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    defines.push_back("_M_ARM");
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_alpha

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_arch_spec_alpha()
{
  set_LP64();
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  long_double_width=16*8;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__alpha__");
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    defines.push_back("_M_ALPHA");
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_mips

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__mips__");
    defines.push_back("mips");
    defines.push_back("_MIPS_SZPTR="+i2string(config.ansi_c.pointer_width));
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    assert(false); // not supported by Visual Studio
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_s390

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_arch_spec_s390()
{
  set_ILP32();
  endianness=endiannesst::IS_BIG_ENDIAN;
  long_double_width=16*8;
  char_is_unsigned=true;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__s390__");
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    assert(false); // not supported by Visual Studio
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_s390x

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_arch_spec_s390x()
{
  set_LP64();
  endianness=endiannesst::IS_BIG_ENDIAN;
  char_is_unsigned=true;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__s390x__");
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    assert(false); // not supported by Visual Studio
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_sparc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__sparc__");
    if(subarch=="sparc64")
      defines.push_back("__arch64__");
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    assert(false); // not supported by Visual Studio
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_ia64

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_arch_spec_ia64()
{
  set_LP64();
  long_double_width=16*8;
  endianness=endiannesst::IS_LITTLE_ENDIAN;
  char_is_unsigned=false;
  NULL_is_zero=true;

  switch(mode)
  {
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__ia64__");
    defines.push_back("_IA64");
    defines.push_back("__IA64__");
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    defines.push_back("_M_IA64");
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_x32

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  case flavourt::MODE_GCC_C:
  case flavourt::MODE_GCC_CPP:
    defines.push_back("__ILP32__");
    defines.push_back("__x86_64");
    defines.push_back("__x86_64__");
    defines.push_back("__amd64__");
    defines.push_back("__amd64");
    break;
  case flavourt::MODE_VISUAL_STUDIO_C_CPP:
    assert(false); // not supported by Visual Studio
    break;
  case flavourt::MODE_CODEWARRIOR_C_CPP:
  case flavourt::MODE_ARM_C_CPP:
  case flavourt::MODE_ANSI_C_CPP:
    break;
  case flavourt::NO_MODE:
    assert(false);
  }
}

/*******************************************************************\

Function: configt::ansi_ct::set_arch_spec_v850

  Inputs: None

 Outputs: None

 Purpose: Sets up the widths of variables for the Renesas V850

\*******************************************************************/

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

/*******************************************************************\

Function: configt::ansi_ct::default_c_standard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

configt::ansi_ct::c_standardt configt::ansi_ct::default_c_standard()
{
  #if defined(__APPLE__)
  // By default, clang on the Mac builds C code in GNU C11
  return c_standardt::C11;
  #elif defined(__FreeBSD__)
  // By default, clang on FreeBSD builds C code in GNU C99
  return c_standardt::C99;
  #else
  return c_standardt::C99;
  #endif
}
  
/*******************************************************************\

Function: configt::ansi_ct::default_cpp_standard

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

configt::cppt::cpp_standardt configt::cppt::default_cpp_standard()
{
  return cpp_standardt::CPP98;
}

/*******************************************************************\

Function: configt::set_arch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  
/*******************************************************************\

Function: configt::set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool configt::set(const cmdlinet &cmdline)
{
  // defaults -- we match the architecture we have ourselves
  
  cpp.cpp_standard=cppt::default_cpp_standard();
  
  ansi_c.single_precision_constant=false;
  ansi_c.for_has_scope=true; // C99 or later
  ansi_c.c_standard=ansi_ct::default_c_standard();
  ansi_c.use_fixed_for_float=false;
  ansi_c.endianness=ansi_ct::endiannesst::NO_ENDIANNESS;
  ansi_c.os=ansi_ct::ost::NO_OS;
  ansi_c.arch="none";
  ansi_c.lib=configt::ansi_ct::libt::LIB_NONE;
  ansi_c.NULL_is_zero=(size_t)((void*)0)==0;
  
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
    if(CLASSPATH!=NULL)
      set_classpath(CLASSPATH);
    else
      set_classpath("."); // default
  }

  if(cmdline.isset("include"))
    ansi_c.include_files=cmdline.get_values("include");

  if(cmdline.isset("floatbv"))
    ansi_c.use_fixed_for_float=false;

  if(cmdline.isset("fixedbv"))
    ansi_c.use_fixed_for_float=true;

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
      ansi_c.preprocessor=ansi_ct::preprocessort::PP_GCC;
      ansi_c.mode=ansi_ct::flavourt::MODE_GCC_C;

      // enable Cygwin
      #ifdef _WIN32
      ansi_c.defines.push_back("__CYGWIN__");
      #endif
    }
    else
    {
      // On Windows, our default is Visual Studio.
      // On FreeBSD, it's clang.
      // On anything else, it's GCC as the preprocessor,
      // but we recognize the Visual Studio language,
      // which is somewhat inconsistent.
      #ifdef _WIN32
      ansi_c.preprocessor=ansi_ct::preprocessort::PP_VISUAL_STUDIO;
      ansi_c.mode=ansi_ct::flavourt::MODE_VISUAL_STUDIO_C_CPP;
      #elif __FreeBSD__
      ansi_c.preprocessor=ansi_ct::preprocessort::PP_CLANG;
      ansi_c.mode=ansi_ct::flavourt::MODE_VISUAL_STUDIO_C_CPP;
      #else
      ansi_c.preprocessor=ansi_ct::preprocessort::PP_GCC;
      ansi_c.mode=ansi_ct::flavourt::MODE_VISUAL_STUDIO_C_CPP;
      #endif
    }
  }
  else if(os=="macos")
  {
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_MACOS;
    ansi_c.mode=ansi_ct::flavourt::MODE_GCC_C;
    ansi_c.preprocessor=ansi_ct::preprocessort::PP_GCC;
  }
  else if(os=="linux" || os=="solaris")
  {
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_LINUX;
    ansi_c.mode=ansi_ct::flavourt::MODE_GCC_C;
    ansi_c.preprocessor=ansi_ct::preprocessort::PP_GCC;
  }
  else if(os=="freebsd")
  {
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_LINUX;
    ansi_c.mode=ansi_ct::flavourt::MODE_GCC_C;
    ansi_c.preprocessor=ansi_ct::preprocessort::PP_CLANG;
  }
  else
  {
    // give up, but use reasonable defaults
    ansi_c.lib=configt::ansi_ct::libt::LIB_FULL;
    ansi_c.os=configt::ansi_ct::ost::OS_LINUX;
    ansi_c.mode=ansi_ct::flavourt::MODE_GCC_C;
    ansi_c.preprocessor=ansi_ct::preprocessort::PP_GCC;
  }

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
    assert(ansi_c.int_width==sizeof(int)*8);
    assert(ansi_c.long_int_width==sizeof(long)*8);
    assert(ansi_c.bool_width==sizeof(bool)*8);
    assert(ansi_c.char_width==sizeof(char)*8);
    assert(ansi_c.short_int_width==sizeof(short)*8);
    assert(ansi_c.long_long_int_width==sizeof(long long)*8);
    assert(ansi_c.pointer_width==sizeof(void *)*8);
    assert(ansi_c.single_width==sizeof(float)*8);
    assert(ansi_c.double_width==sizeof(double)*8);
    assert(ansi_c.char_is_unsigned==(char(255)==255));

    #ifndef _WIN32
    // On Windows, long double width varies by compiler
    assert(ansi_c.long_double_width==sizeof(long double)*8);
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

  return false;
}

/*******************************************************************\

Function: configt::ansi_ct::os_to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string configt::ansi_ct::os_to_string(ost os)
{
  switch(os)
  {
  case ost::OS_LINUX: return "linux";
  case ost::OS_MACOS: return "macos";
  case ost::OS_WIN: return "win";
  default: return "none";
  }
}

/*******************************************************************\

Function: configt::ansi_ct::string_to_os

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: string_from_ns

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static irep_idt string_from_ns(
  const namespacet &ns,
  const std::string &what)
{
  const irep_idt id=CPROVER_PREFIX "architecture_"+what;
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
    throw "failed to find "+id2string(id);
    
  const exprt &tmp=symbol->value;
  
  if(tmp.id()!=ID_address_of ||
     tmp.operands().size()!=1 ||
     tmp.op0().id()!=ID_index ||
     tmp.op0().operands().size()!=2 ||
     tmp.op0().op0().id()!=ID_string_constant)
  {
    throw "symbol table configuration entry `"+id2string(id)+"' is not a string constant";
  }

  return tmp.op0().op0().get(ID_value);
}

/*******************************************************************\

Function: unsigned_from_ns

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static unsigned unsigned_from_ns(
  const namespacet &ns,
  const std::string &what)
{
  const irep_idt id=CPROVER_PREFIX "architecture_"+what;
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
    throw "failed to find "+id2string(id);
    
  exprt tmp=symbol->value;
  simplify(tmp, ns);
  
  if(tmp.id()!=ID_constant)
    throw "symbol table configuration entry `"+id2string(id)+"' is not a constant";
  
  mp_integer int_value;
  
  if(to_integer(to_constant_expr(tmp), int_value))
    throw "failed to convert symbol table configuration entry `"+id2string(id)+"'";
    
  return integer2unsigned(int_value);
}

/*******************************************************************\

Function: configt::set_from_symbol_table

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  ansi_c.use_fixed_for_float=unsigned_from_ns(ns, "fixed_for_float")!=0;
  // for_has_scope, single_precision_constant, rounding_mode not
  // stored in namespace

  ansi_c.alignment=unsigned_from_ns(ns, "alignment");

  ansi_c.memory_operand_size=unsigned_from_ns(ns, "memory_operand_size");

  ansi_c.endianness=(ansi_ct::endiannesst)unsigned_from_ns(ns, "endianness");

  if(symbol_table.symbols.find(CPROVER_PREFIX "architecture_" "os")==
     symbol_table.symbols.end())
    ansi_c.os=ansi_ct::string_to_os(id2string(this_operating_system()));
  else
    ansi_c.os=ansi_ct::string_to_os(id2string(string_from_ns(ns, "os")));

  //NULL_is_zero=from_ns("NULL_is_zero");
  ansi_c.NULL_is_zero=true;

  // mode, preprocessor (and all preprocessor command line options),
  // lib, string_abstraction not stored in namespace
}

/*******************************************************************\

Function: configt::ansi_ct::this_architecture

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt configt::this_architecture()
{
  irep_idt this_arch;
  
  // following http://wiki.debian.org/ArchitectureSpecificsMemo

  #ifdef __alpha__
  this_arch="alpha";
  #elif __armel__
  this_arch="armel";
  #elif __aarch64__
  this_arch="arm64";
  #elif __arm__
    #ifdef __ARM_PCS_VFP
    this_arch="armhf"; // variant of arm with hard float
    #else
    this_arch="arm";
    #endif
  #elif __mipsel__
    #if _MIPS_SIM==_ABIO32
    this_arch="mipsel";
    #elif _MIPS_SIM==_ABIN32
    this_arch="mipsn32el";
    #else
    this_arch="mips64el";
    #endif
  #elif __mips__
    #if _MIPS_SIM==_ABIO32
    this_arch="mips";
    #elif _MIPS_SIM==_ABIN32
    this_arch="mipsn32";
    #else
    this_arch="mips64";
    #endif
  #elif __powerpc__
    #if defined(__ppc64__) || defined(__PPC64__) || defined(__powerpc64__) || defined(__POWERPC64__)
      #ifdef __LITTLE_ENDIAN__
      this_arch="ppc64le";
      #else
      this_arch="ppc64";
      #endif
    #else
    this_arch="powerpc";
    #endif
  #elif __sparc__
    #ifdef __arch64__
    this_arch="sparc64";
    #else
    this_arch="sparc";
    #endif
  #elif __ia64__
  this_arch="ia64";
  #elif __s390x__
  this_arch="s390x";
  #elif __s390__
  this_arch="s390";
  #elif __x86_64__
    #ifdef __ILP32__
    this_arch="x32"; // variant of x86_64 with 32-bit pointers
    #else
    this_arch="x86_64";
    #endif
  #elif __i386__
  this_arch="i386";
  #elif _WIN64
  this_arch="x86_64";
  #elif _WIN32
  this_arch="i386";
  #else
  // something new and unknown!
  this_arch="unknown";
  #endif

  return this_arch;  
}

/*******************************************************************\

Function: configt::set_classpath

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::set_classpath(const std::string &cp)
{
  std::string current;
  for(std::size_t pos=0; pos<cp.size(); pos++)
  {
    // these are separated by colons
    if(cp[pos]==':')
    {
      if(!current.empty()) java.class_path.push_back(current);
    }
    else
      current+=cp[pos];
  }
  
  if(!current.empty()) java.class_path.push_back(current);
}

/*******************************************************************\

Function: configt::ansi_ct::this_operating_system

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
