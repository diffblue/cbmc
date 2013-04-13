/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/i2string.h>
#include <util/config.h>

#include "internal_additions.h"

const char gcc_builtin_headers_generic[]=
"# 1 \"gcc_builtin_headers_generic.h\"\n"
#include "gcc_builtin_headers_generic.inc"
;

const char gcc_builtin_headers_ia32[]=
"# 1 \"gcc_builtin_headers_ia32.h\"\n"
#include "gcc_builtin_headers_ia32.inc"
;

const char gcc_builtin_headers_alpha[]=
"# 1 \"gcc_builtin_headers_alpha.h\"\n"
#include "gcc_builtin_headers_alpha.inc"
;

const char gcc_builtin_headers_arm[]=
"# 1 \"gcc_builtin_headers_arm.h\"\n"
#include "gcc_builtin_headers_arm.inc"
;

const char gcc_builtin_headers_mips[]=
"# 1 \"gcc_builtin_headers_mips.h\"\n"
#include "gcc_builtin_headers_mips.inc"
;

const char gcc_builtin_headers_power[]=
"# 1 \"gcc_builtin_headers_power.h\"\n"
#include "gcc_builtin_headers_power.inc"
;

const char arm_builtin_headers[]=
"# 1 \"arm_builtin_headers.h\"\n"
#include "arm_builtin_headers.inc"
;

const char cw_builtin_headers[]=
"# 1 \"cw_builtin_headers.h\"\n"
#include "cw_builtin_headers.inc"
;

/*******************************************************************\

Function: architecture_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string architecture_string(int value, const char *s)
{
  return std::string("const int __CPROVER_architecture_")+
         std::string(s)+
         "="+i2string(value)+";\n";
}

/*******************************************************************\

Function: ansi_c_internal_additions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_internal_additions(std::string &code)
{
  code+=
    "# 1 \"<built-in-additions>\"\n"
    "typedef __typeof__(sizeof(int)) __CPROVER_size_t;\n"
    "void __CPROVER_assume(__CPROVER_bool assumption);\n"
    "void __VERIFIER_assume(__CPROVER_bool assumption);\n"
    "void assert(__CPROVER_bool assertion);\n"
    "void __CPROVER_assert(__CPROVER_bool assertion, const char *description);\n"
    "__CPROVER_bool __CPROVER_equal();\n"
    "__CPROVER_bool __CPROVER_same_object(const void *, const void *);\n"
    "__CPROVER_bool __CPROVER_is_zero_string(const void *);\n"
    "__CPROVER_size_t __CPROVER_zero_string_length(const void *);\n"
    "__CPROVER_size_t __CPROVER_buffer_size(const void *);\n"

    "const unsigned __CPROVER_constant_infinity_uint;\n"
    "typedef void __CPROVER_integer;\n"
    "typedef void __CPROVER_rational;\n"
    "void __CPROVER_initialize(void);\n"
    "void __CPROVER_input(const char *id, ...);\n"
    "void __CPROVER_output(const char *id, ...);\n"
    "void __CPROVER_cover(__CPROVER_bool condition);\n"
    
    // concurrency-related
    "void __CPROVER_atomic_begin();\n"
    "void __CPROVER_atomic_end();\n"
    "void __CPROVER_fence(const char *kind, ...);\n"
    "unsigned long long __CPROVER_threads_exited=0;\n"
    "unsigned long __CPROVER_next_thread_id=0;\n"

    // traces
    "void CBMC_trace(int lvl, const char *event, ...);\n"
    
    // pointers
    "unsigned __CPROVER_POINTER_OBJECT(const void *p);\n"
    "signed __CPROVER_POINTER_OFFSET(const void *p);\n"
    "__CPROVER_bool __CPROVER_DYNAMIC_OBJECT(const void *p);\n"
    "extern unsigned char __CPROVER_memory[__CPROVER_constant_infinity_uint];\n"
    
    // malloc
    "void *__CPROVER_malloc(__CPROVER_size_t size);\n"
    "const void *__CPROVER_deallocated=0;\n"
    "const void *__CPROVER_malloc_object=0;\n"
    "__CPROVER_size_t __CPROVER_malloc_size;\n"
    "__CPROVER_bool __CPROVER_malloc_is_new_array=0;\n" // for the benefit of C++

    // this is ANSI-C
    "extern __CPROVER_thread_local const char __func__[__CPROVER_constant_infinity_uint];\n"
    
    // this is GCC
    "extern __CPROVER_thread_local const char __FUNCTION__[__CPROVER_constant_infinity_uint];\n"
    "extern __CPROVER_thread_local const char __PRETTY_FUNCTION__[__CPROVER_constant_infinity_uint];\n"

    // float stuff
    "__CPROVER_bool __CPROVER_isnan(double f);\n"
    "__CPROVER_bool __CPROVER_isfinite(double f);\n"
    "__CPROVER_bool __CPROVER_isinf(double f);\n"
    "__CPROVER_bool __CPROVER_isnormal(double f);\n"
    "__CPROVER_bool __CPROVER_sign(double f);\n"
    "double __CPROVER_inf(void);\n"
    "float __CPROVER_inff(void);\n"
    "long double __CPROVER_infl(void);\n"
    "int __CPROVER_thread_local __CPROVER_rounding_mode="+i2string(config.ansi_c.rounding_mode)+";\n"

    // absolute value
    "int __CPROVER_abs(int x);\n"
    "long int __CPROVER_labs(long int x);\n"
    "double __CPROVER_fabs(double x);\n"
    "long double __CPROVER_fabsl(long double x);\n"
    "float __CPROVER_fabsf(float x);\n"
    
    // arrays
    "__CPROVER_bool __CPROVER_array_equal(const void *array1, const void *array2);\n"
    "void __CPROVER_array_copy(const void *dest, const void *src);\n"
    "void __CPROVER_array_set(const void *dest, ...);\n"

    // k-induction
    "void __CPROVER_k_induction_hint(unsigned min, unsigned max, "
      "unsigned step, unsigned loop_free);\n"
    
    // manual specification of predicates
    "void __CPROVER_predicate(__CPROVER_bool predicate);\n"
    "void __CPROVER_parameter_predicates();\n"
    "void __CPROVER_return_predicates();\n"

    "\n";
    
  // GCC junk stuff, also for ARM
  if(config.ansi_c.mode==configt::ansi_ct::MODE_GCC ||
     config.ansi_c.mode==configt::ansi_ct::MODE_ARM)
  {
    code+=gcc_builtin_headers_generic;

    // there are many more, e.g., look at
    // https://developer.apple.com/library/mac/#documentation/developertools/gcc-4.0.1/gcc/Target-Builtins.html

    switch(config.ansi_c.arch)
    {
    case configt::ansi_ct::ARCH_I386:
    case configt::ansi_ct::ARCH_X86_64:
    case configt::ansi_ct::ARCH_X32:
      code+=gcc_builtin_headers_ia32;
      break;
      
    case configt::ansi_ct::ARCH_ARM:
      code+=gcc_builtin_headers_arm;
      break;

    case configt::ansi_ct::ARCH_ALPHA:
      code+=gcc_builtin_headers_alpha;
      break;
     
    case configt::ansi_ct::ARCH_MIPS:
      code+=gcc_builtin_headers_mips;
      break;
     
    case configt::ansi_ct::ARCH_POWER:
      code+=gcc_builtin_headers_power;
      break;
     
    default:;
    }

    // On 64-bit systems, gcc has typedefs
    // __int128_t und __uint128_t -- but not on 32 bit!
    if(config.ansi_c.long_int_width>=64)
    {
      code+="typedef signed __int128 __int128_t;\n"
            "typedef signed __int128 __uint128_t;\n";
    }
  }

  // this is Visual C/C++ only
  if(config.ansi_c.os==configt::ansi_ct::OS_WIN)
    code+="int __noop();\n"
          "int __assume(int);\n";
    
  // ARM stuff
  if(config.ansi_c.mode==configt::ansi_ct::MODE_ARM)
    code+=arm_builtin_headers;
    
  // CW stuff
  if(config.ansi_c.mode==configt::ansi_ct::MODE_CODEWARRIOR)
    code+=cw_builtin_headers;
    
  // Architecture strings
  ansi_c_architecture_strings(code);
}

/*******************************************************************\

Function: architecture_strings

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_architecture_strings(std::string &code)
{
  // The following are CPROVER-specific.
  // They allow identifying the architectural settings used
  // at compile time from a goto-binary.

  code+="# 1 \"<builtin-architecture-strings>\"\n";

  code+=architecture_string(config.ansi_c.bool_width, "bool_width");
  code+=architecture_string(config.ansi_c.int_width, "int_width");
  code+=architecture_string(config.ansi_c.long_int_width, "long_int_width");
  code+=architecture_string(config.ansi_c.char_width, "char_width");
  code+=architecture_string(config.ansi_c.short_int_width, "short_int_width");
  code+=architecture_string(config.ansi_c.long_long_int_width, "long_long_int_width");
  code+=architecture_string(config.ansi_c.pointer_width, "pointer_width");
  code+=architecture_string(config.ansi_c.char_is_unsigned, "char_is_unsigned");
  code+=architecture_string(config.ansi_c.wchar_t_is_unsigned, "wchar_t_is_unsigned");
  code+=architecture_string(config.ansi_c.int_width, "word_size"); // old 
  code+=architecture_string(config.ansi_c.use_fixed_for_float, "fixed_for_float");
  code+=architecture_string(config.ansi_c.alignment, "alignment");
  code+=architecture_string(config.ansi_c.memory_operand_size, "memory_operand_size");
  code+=architecture_string(config.ansi_c.single_width, "single_width");
  code+=architecture_string(config.ansi_c.double_width, "double_width");
  code+=architecture_string(config.ansi_c.long_double_width, "long_double_width");
  code+=architecture_string(config.ansi_c.wchar_t_width, "wchar_t_width");
  code+=architecture_string(config.ansi_c.endianness, "endianness");
}
