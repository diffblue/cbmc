/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <i2string.h>
#include <config.h>

#include "gcc_builtin_headers.h"
#include "arm_builtin_headers.h"
#include "internal_additions.h"

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
    "typedef __typeof__(sizeof(int)) __CPROVER_size_t;\n"
    "void __CPROVER_assume(_Bool assumption);\n"
    "void __VERIFIER_assume(_Bool assumption);\n"
    "void assert(_Bool assertion);\n"
    "void __CPROVER_assert(_Bool assertion, const char *description);\n"
    "_Bool __CPROVER_equal();\n"
    "_Bool __CPROVER_same_object(const void *, const void *);\n"
    "_Bool __CPROVER_is_zero_string(const void *);\n"
    "__CPROVER_size_t __CPROVER_zero_string_length(const void *);\n"
    "__CPROVER_size_t __CPROVER_buffer_size(const void *);\n"

    "const unsigned __CPROVER_constant_infinity_uint;\n"
    "typedef void __CPROVER_integer;\n"
    "typedef void __CPROVER_rational;\n"
    "void __CPROVER_initialize(void);\n"
    "void __CPROVER_input(const char *id, ...);\n"
    "void __CPROVER_output(const char *id, ...);\n"
    "void __CPROVER_cover(_Bool condition);\n"
    "void __CPROVER_atomic_begin();\n"
    "void __CPROVER_atomic_end();\n"

    // traces
    "void CBMC_trace(int lvl, const char *event, ...);\n"
    
    // pointers
    "unsigned __CPROVER_POINTER_OBJECT(const void *p);\n"
    "signed __CPROVER_POINTER_OFFSET(const void *p);\n"
    "_Bool __CPROVER_DYNAMIC_OBJECT(const void *p);\n"
    "extern unsigned char __CPROVER_memory[__CPROVER_constant_infinity_uint];\n"
    
    // malloc
    "void *__CPROVER_malloc(__CPROVER_size_t size);\n"
    "const void *__CPROVER_deallocated=0;\n"
    "const void *__CPROVER_malloc_object=0;\n"
    "__CPROVER_size_t __CPROVER_malloc_size;\n"
    "_Bool __CPROVER_malloc_is_new_array=0;\n" // for the benefit of C++

    // this is ANSI-C
    "extern __CPROVER_thread_local const char __func__[__CPROVER_constant_infinity_uint];\n"
    
    // this is GCC
    "extern __CPROVER_thread_local const char __FUNCTION__[__CPROVER_constant_infinity_uint];\n"
    "extern __CPROVER_thread_local const char __PRETTY_FUNCTION__[__CPROVER_constant_infinity_uint];\n"

    // float stuff
    "_Bool __CPROVER_isnan(double f);\n"
    "_Bool __CPROVER_isfinite(double f);\n"
    "_Bool __CPROVER_isinf(double f);\n"
    "_Bool __CPROVER_isnormal(double f);\n"
    "_Bool __CPROVER_sign(double f);\n"
    "extern int __CPROVER_rounding_mode;\n"

    // absolute value
    "int __CPROVER_abs(int x);\n"
    "long int __CPROVER_labs(long int x);\n"
    "double __CPROVER_fabs(double x);\n"
    "long double __CPROVER_fabsl(long double x);\n"
    "float __CPROVER_fabsf(float x);\n"
    
    // arrays
    "_Bool __CPROVER_array_equal(const void array1[], const void array2[]);\n"
    "void __CPROVER_array_copy(const void dest[], const void src[]);\n"
    "void __CPROVER_array_set(const void dest[], ...);\n"

    // k-induction
    "void __CPROVER_k_induction_hint(unsigned min, unsigned max, "
      "unsigned step, unsigned loop_free);\n"
    
    // manual specification of predicates
    "void __CPROVER_predicate(_Bool predicate);\n"
    "void __CPROVER_parameter_predicates();\n"
    "void __CPROVER_return_predicates();\n"

    // GCC junk stuff
    GCC_BUILTIN_HEADERS

    "\n";

  if(config.ansi_c.os==configt::ansi_ct::OS_WIN)
    code+="int __noop();\n"; // this is Visual C/C++
    
  // ARM stuff
  if(config.ansi_c.mode==configt::ansi_ct::MODE_ARM)
    code+=ARM_BUILTIN_HEADERS;
    
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
  code+=architecture_string(config.ansi_c.bool_width, "bool_width");
  code+=architecture_string(config.ansi_c.int_width, "int_width");
  code+=architecture_string(config.ansi_c.long_int_width, "long_int_width");
  code+=architecture_string(config.ansi_c.char_width, "char_width");
  code+=architecture_string(config.ansi_c.short_int_width, "short_int_width");
  code+=architecture_string(config.ansi_c.long_long_int_width, "long_long_int_width");
  code+=architecture_string(config.ansi_c.pointer_width, "pointer_width");
  code+=architecture_string(config.ansi_c.char_is_unsigned, "char_is_unsigned");
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
