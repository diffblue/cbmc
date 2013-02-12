/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "namespace.h"
#include "config.h"
#include "symbol_table.h"
#include "arith_tools.h"
#include "cmdline.h"
#include "simplify_expr.h"

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

Function: configt::ansi_ct::set

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool configt::set(const cmdlinet &cmdline)
{
  // defaults -- we match the architecture we have ourselves

  // ealier than C99
  ansi_c.for_has_scope=false;

  if(sizeof(long int)==8)
    ansi_c.set_64();
  else
    ansi_c.set_32();
    
  ansi_c.use_fixed_for_float=false;
  ansi_c.endianness=ansi_ct::NO_ENDIANNESS;
  ansi_c.os=ansi_ct::NO_OS;
  ansi_c.arch=ansi_ct::NO_ARCH;
  ansi_c.lib=configt::ansi_ct::LIB_NONE;
  ansi_c.rounding_mode=ieee_floatt::ROUND_TO_EVEN;

  #ifdef _WIN32

  if(cmdline.isset("gcc"))
    ansi_c.mode=ansi_ct::MODE_GCC;
  else
    ansi_c.mode=ansi_ct::MODE_VISUAL_STUDIO;

  #else
  ansi_c.mode=ansi_ct::MODE_GCC;
  #endif

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
    
  if(cmdline.isset("function"))
    main=cmdline.getval("function");
    
  if(cmdline.isset('D'))
    ansi_c.defines=cmdline.get_values('D');

  if(cmdline.isset('I'))
    ansi_c.include_paths=cmdline.get_values('I');

  if(cmdline.isset("include"))
    ansi_c.include_files=cmdline.get_values("include");

  if(cmdline.isset("floatbv"))
    ansi_c.use_fixed_for_float=false;

  if(cmdline.isset("fixedbv"))
    ansi_c.use_fixed_for_float=true;

  if(cmdline.isset("i386-linux"))
  {
    ansi_c.mode=ansi_ct::MODE_GCC;
    ansi_c.os=configt::ansi_ct::OS_LINUX;
    ansi_c.arch=configt::ansi_ct::ARCH_I386;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.lib=configt::ansi_ct::LIB_FULL;
  }

  if(cmdline.isset("i386-win32") ||
     cmdline.isset("win32"))
  {
    ansi_c.mode=ansi_ct::MODE_VISUAL_STUDIO;
    ansi_c.os=configt::ansi_ct::OS_WIN;
    ansi_c.arch=configt::ansi_ct::ARCH_I386;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.lib=configt::ansi_ct::LIB_FULL;
    ansi_c.set_32();
    
    // On Windows, wchar_t is unsigned 16 bit, and
    // long double is the same as double.
    ansi_c.wchar_t_width=2*8;
    ansi_c.wchar_t_is_unsigned=true;
    ansi_c.long_double_width=8*8;
  }

  if(cmdline.isset("winx64"))
  {
    ansi_c.mode=ansi_ct::MODE_VISUAL_STUDIO;
    ansi_c.os=configt::ansi_ct::OS_WIN;
    ansi_c.arch=configt::ansi_ct::ARCH_X86_64;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.lib=configt::ansi_ct::LIB_FULL;
    // note that sizeof(void *)==8, but sizeof(long)==4!
    ansi_c.set_LLP64();

    // On Windows, wchar_t is unsigned 16 bit, and
    // long double is the same as double.
    ansi_c.wchar_t_width=2*8;
    ansi_c.wchar_t_is_unsigned=true;
    ansi_c.long_double_width=8*8;
  }

  if(cmdline.isset("i386-macos"))
  {
    ansi_c.mode=ansi_ct::MODE_GCC;
    ansi_c.os=configt::ansi_ct::OS_MACOS;
    ansi_c.arch=configt::ansi_ct::ARCH_I386;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.lib=configt::ansi_ct::LIB_FULL;
  }

  if(cmdline.isset("ppc-macos"))
  {
    ansi_c.mode=ansi_ct::MODE_GCC;
    ansi_c.os=configt::ansi_ct::OS_MACOS;
    ansi_c.arch=configt::ansi_ct::ARCH_POWER;
    ansi_c.endianness=configt::ansi_ct::IS_BIG_ENDIAN;
    ansi_c.lib=configt::ansi_ct::LIB_FULL;
  }
  
  if(cmdline.isset("no-arch"))
  {
    ansi_c.os=configt::ansi_ct::NO_OS;
    ansi_c.arch=configt::ansi_ct::NO_ARCH;
    ansi_c.endianness=configt::ansi_ct::NO_ENDIANNESS;
    ansi_c.lib=configt::ansi_ct::LIB_NONE;
  }
  else if(ansi_c.os==configt::ansi_ct::NO_OS)
  {
    // this is the default
    ansi_c.lib=configt::ansi_ct::LIB_FULL;
    
    // following http://wiki.debian.org/ArchitectureSpecificsMemo

    #ifdef __alpha__
    ansi_c.arch=configt::ansi_ct::ARCH_ALPHA;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.long_double_width=16*8;
    ansi_c.long_int_width=8*8;
    ansi_c.pointer_width=8*8;
    ansi_c.char_is_unsigned=false;
    #elif __armel__
    ansi_c.arch=configt::ansi_ct::ARCH_ARM;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.long_double_width=8*8;
    ansi_c.char_is_unsigned=true;
    #elif __arm64__
    ansi_c.arch=configt::ansi_ct::ARCH_ARM;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.long_int_width=8*8;
    ansi_c.pointer_width=8*8;
    ansi_c.long_double_width=16*8;
    ansi_c.char_is_unsigned=true;
    #elif __arm__
    ansi_c.arch=configt::ansi_ct::ARCH_ARM;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.long_double_width=8*8;
    ansi_c.char_is_unsigned=true;
    #elif __mipsel__
    ansi_c.arch=configt::ansi_ct::ARCH_MIPS;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.long_double_width=8*8;
    ansi_c.char_is_unsigned=false;
    #elif __mips__
    ansi_c.arch=configt::ansi_ct::ARCH_MIPS;
    ansi_c.endianness=configt::ansi_ct::IS_BIG_ENDIAN;
    ansi_c.long_double_width=8*8;
    ansi_c.char_is_unsigned=false;
    #elif __powerpc__
    ansi_c.arch=configt::ansi_ct::ARCH_POWER;
    ansi_c.endianness=configt::ansi_ct::IS_BIG_ENDIAN;
    ansi_c.long_double_width=16*8;
    ansi_c.char_is_unsigned=true;
    #elif __sparc__
    ansi_c.arch=configt::ansi_ct::ARCH_SPARC;
    ansi_c.endianness=configt::ansi_ct::IS_BIG_ENDIAN;
    ansi_c.long_double_width=16*8;
    ansi_c.char_is_unsigned=false;
    #elif __ia64__
    ansi_c.arch=configt::ansi_ct::ARCH_IA64;
    ansi_c.long_int_width=8*8;
    ansi_c.pointer_width=8*8;
    ansi_c.long_double_width=16*8;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.char_is_unsigned=false;
    #elif __s390x__
    ansi_c.arch=configt::ansi_ct::ARCH_S390X;
    ansi_c.long_int_width=8*8;
    ansi_c.pointer_width=8*8;
    ansi_c.endianness=configt::ansi_ct::IS_BIG_ENDIAN;
    ansi_c.char_is_unsigned=true;
    #elif __s390__
    ansi_c.arch=configt::ansi_ct::ARCH_S390;
    ansi_c.endianness=configt::ansi_ct::IS_BIG_ENDIAN;
    ansi_c.long_double_width=16*8;
    ansi_c.char_is_unsigned=true;
    #elif __x86_64__
    ansi_c.arch=configt::ansi_ct::ARCH_X86_64;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.long_double_width=16*8;
    ansi_c.pointer_width=8*8;
    ansi_c.char_is_unsigned=false;
    #elif __i386__
    ansi_c.arch=configt::ansi_ct::ARCH_I386;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.char_is_unsigned=false;
    #else
    // something new and unknown!
    ansi_c.arch=configt::ansi_ct::ARCH_I386;
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    ansi_c.char_is_unsigned=false;
    #endif

    #ifdef _WIN32
    ansi_c.os=configt::ansi_ct::OS_WIN;
    ansi_c.wchar_t_width=2*8;
    ansi_c.wchar_t_is_unsigned=true;
    ansi_c.long_double_width=8*8;
    #elif __APPLE__
    ansi_c.os=configt::ansi_ct::OS_MACOS;
    #else
    ansi_c.os=configt::ansi_ct::OS_LINUX;
    #endif
  }
  
  if(cmdline.isset("string-abstraction"))
    ansi_c.string_abstraction=true;
  else
    ansi_c.string_abstraction=false;  
  
  if(cmdline.isset("no-library"))
    ansi_c.lib=configt::ansi_ct::LIB_NONE;
  
  if(cmdline.isset("little-endian"))
    ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;

  if(cmdline.isset("big-endian"))
    ansi_c.endianness=configt::ansi_ct::IS_BIG_ENDIAN;

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

Function: configt::ansi_ct::set_from_symbol_table

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int configt::ansi_ct::from_ns(const namespacet &ns, const std::string &what)
{
  const irep_idt id="c::__CPROVER_architecture_"+what;
  const symbolt *symbol;

  if(ns.lookup(id, symbol))
    throw "failed to find "+id2string(id);
    
  exprt tmp=symbol->value;
  simplify(tmp, ns);
  
  mp_integer int_value;
  
  if(to_integer(tmp, int_value))
    throw "failed to convert symbol table configuration entry `"+id2string(id)+"'";
    
  return integer2long(int_value);
}

/*******************************************************************\

Function: configt::ansi_ct::set_from_symbol_table

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void configt::ansi_ct::set_from_symbol_table(const symbol_tablet &symbol_table)
{
  namespacet ns(symbol_table);

  bool_width=1*8;
  int_width=from_ns(ns, "int_width");
  long_int_width=from_ns(ns, "long_int_width");
  long_int_width=from_ns(ns, "long_int_width");
  char_width=from_ns(ns, "char_width");
  short_int_width=from_ns(ns, "short_int_width");
  long_long_int_width=from_ns(ns, "long_long_int_width");
  pointer_width=from_ns(ns, "pointer_width");
  single_width=from_ns(ns, "single_width");
  double_width=from_ns(ns, "double_width");
  long_double_width=from_ns(ns, "long_double_width");
  char_is_unsigned=from_ns(ns, "char_is_unsigned");
  wchar_t_width=from_ns(ns, "wchar_t_width");
  alignment=from_ns(ns, "alignment");
  use_fixed_for_float=from_ns(ns, "fixed_for_float");
  endianness=(endiannesst)from_ns(ns, "endianness");

  //memory_operand_size=from_ns(ns, "memory_operand_size");
  memory_operand_size=int_width/8;
}

