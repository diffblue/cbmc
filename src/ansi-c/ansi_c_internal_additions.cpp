/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_internal_additions.h"

#include <util/c_types.h>
#include <util/config.h>

#include <goto-programs/adjust_float_expressions.h>

#include <linking/static_lifetime_init.h>

#include "ansi_c_parser.h"

const char gcc_builtin_headers_types[] =
  "#line 1 \"gcc_builtin_headers_types.h\"\n"
#include "compiler_headers/gcc_builtin_headers_types.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_generic[] =
  "#line 1 \"gcc_builtin_headers_generic.h\"\n"
#include "compiler_headers/gcc_builtin_headers_generic.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_math[] =
  "#line 1 \"gcc_builtin_headers_math.h\"\n"
#include "compiler_headers/gcc_builtin_headers_math.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_mem_string[] =
  "#line 1 \"gcc_builtin_headers_mem_string.h\"\n"
// NOLINTNEXTLINE(whitespace/line_length)
#include "compiler_headers/gcc_builtin_headers_mem_string.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_omp[] = "#line 1 \"gcc_builtin_headers_omp.h\"\n"
#include "compiler_headers/gcc_builtin_headers_omp.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_tm[] = "#line 1 \"gcc_builtin_headers_tm.h\"\n"
#include "compiler_headers/gcc_builtin_headers_tm.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_ubsan[] =
  "#line 1 \"gcc_builtin_headers_ubsan.h\"\n"
#include "compiler_headers/gcc_builtin_headers_ubsan.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_ia32[] =
  "#line 1 \"gcc_builtin_headers_ia32.h\"\n"
#include "compiler_headers/gcc_builtin_headers_ia32.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_2[] =
#include "compiler_headers/gcc_builtin_headers_ia32-2.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_3[] =
#include "compiler_headers/gcc_builtin_headers_ia32-3.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_4[] =
#include "compiler_headers/gcc_builtin_headers_ia32-4.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_5[] =
#include "compiler_headers/gcc_builtin_headers_ia32-5.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_6[] =
#include "compiler_headers/gcc_builtin_headers_ia32-6.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_7[] =
#include "compiler_headers/gcc_builtin_headers_ia32-7.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_8[] =
#include "compiler_headers/gcc_builtin_headers_ia32-8.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_9[] =
#include "compiler_headers/gcc_builtin_headers_ia32-9.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_alpha[] =
  "#line 1 \"gcc_builtin_headers_alpha.h\"\n"
#include "compiler_headers/gcc_builtin_headers_alpha.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_arm[] = "#line 1 \"gcc_builtin_headers_arm.h\"\n"
#include "compiler_headers/gcc_builtin_headers_arm.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_mips[] =
  "#line 1 \"gcc_builtin_headers_mips.h\"\n"
#include "compiler_headers/gcc_builtin_headers_mips.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_power[] =
  "#line 1 \"gcc_builtin_headers_power.h\"\n"
#include "compiler_headers/gcc_builtin_headers_power.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char arm_builtin_headers[] = "#line 1 \"arm_builtin_headers.h\"\n"
#include "compiler_headers/arm_builtin_headers.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char cw_builtin_headers[] = "#line 1 \"cw_builtin_headers.h\"\n"
#include "compiler_headers/cw_builtin_headers.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char clang_builtin_headers[] = "#line 1 \"clang_builtin_headers.h\"\n"
#include "compiler_headers/clang_builtin_headers.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

const char cprover_builtin_headers[] = "#line 1 \"cprover_builtin_headers.h\"\n"
#include "cprover_builtin_headers.inc" // IWYU pragma: keep
  ;                                    // NOLINT(whitespace/semicolon)

const char windows_builtin_headers[] = "#line 1 \"windows_builtin_headers.h\"\n"
#include "compiler_headers/windows_builtin_headers.inc" // IWYU pragma: keep
  ; // NOLINT(whitespace/semicolon)

static std::string architecture_string(const std::string &value, const char *s)
{
  return std::string("const char *" CPROVER_PREFIX "architecture_") +
         std::string(s) + "=\"" + value + "\";\n";
}

template <typename T>
static std::string architecture_string(T value, const char *s)
{
  return std::string("const " CPROVER_PREFIX "integer " CPROVER_PREFIX
                     "architecture_") +
         std::string(s) + "=" + std::to_string(value) + ";\n";
}

void ansi_c_internal_additions(std::string &code, bool support_float16_type)
{
  // clang-format off
  // do the built-in types and variables
  code+=
    "#line 1 \"<built-in-additions>\"\n"
    "typedef __typeof__(sizeof(int)) " CPROVER_PREFIX "size_t;\n"
    "typedef "+c_type_as_string(signed_size_type().get(ID_C_c_type))+
      " " CPROVER_PREFIX "ssize_t;\n"
    "const unsigned " CPROVER_PREFIX "constant_infinity_uint;\n"
    "typedef void " CPROVER_PREFIX "integer;\n"
    "typedef void " CPROVER_PREFIX "rational;\n"
    "extern unsigned char " CPROVER_PREFIX "memory["
      CPROVER_PREFIX "constant_infinity_uint];\n"

    // malloc
    "const void *" CPROVER_PREFIX "deallocated=0;\n"
    "const void *" CPROVER_PREFIX "dead_object=0;\n"
    "const void *" CPROVER_PREFIX "memory_leak=0;\n"
    "void *" CPROVER_PREFIX "allocate("
      CPROVER_PREFIX "size_t size, " CPROVER_PREFIX "bool zero);\n"
    "void " CPROVER_PREFIX "deallocate(void *);\n"

    CPROVER_PREFIX "thread_local " CPROVER_PREFIX "size_t "
      CPROVER_PREFIX "max_malloc_size="+
      integer2string(config.max_malloc_size());
  if(config.ansi_c.pointer_width==config.ansi_c.long_int_width)
    code += "UL;\n";
  else if(config.ansi_c.pointer_width==config.ansi_c.long_long_int_width)
    code += "ULL;\n";
  else
    code += "U;\n";

  code+=
    // this is ANSI-C
    "extern " CPROVER_PREFIX "thread_local const char __func__["
      CPROVER_PREFIX "constant_infinity_uint];\n"

    // this is GCC
    "extern " CPROVER_PREFIX "thread_local const char __FUNCTION__["
      CPROVER_PREFIX "constant_infinity_uint];\n"
    "extern " CPROVER_PREFIX "thread_local const char __PRETTY_FUNCTION__["
      CPROVER_PREFIX "constant_infinity_uint];\n"

    // float stuff
    "int " CPROVER_PREFIX "thread_local " +
      id2string(rounding_mode_identifier()) + '='+
      std::to_string(config.ansi_c.rounding_mode)+";\n"

    // pipes, write, read, close
    "struct " CPROVER_PREFIX "pipet {\n"
    "  _Bool widowed;\n"
    "  char data[4];\n"
    "  short next_avail;\n"
    "  short next_unread;\n"
    "};\n"
    "\n"
    // This function needs to be declared, or otherwise can't be called
    // by the entry-point construction.
    "void " INITIALIZE_FUNCTION "(void);\n"
    "\n"
    // frame specifications for contracts
    // Declares a range of bytes as assignable (internal representation)
    "void " CPROVER_PREFIX "assignable(void *ptr,\n"
    "  " CPROVER_PREFIX "size_t size,\n"
    "  " CPROVER_PREFIX "bool is_ptr_to_ptr);\n"
    // Declares a range of bytes as assignable
    "void " CPROVER_PREFIX "object_upto(void *ptr, \n"
    "  " CPROVER_PREFIX "size_t size);\n"
    // Declares bytes from ptr to the end of the object as assignable
    "void " CPROVER_PREFIX "object_from(void *ptr);\n"
    // Declares the whole object pointed to by ptr as assignable
    "void " CPROVER_PREFIX "object_whole(void *ptr);\n"
    // Declares a pointer as freeable
    "void " CPROVER_PREFIX "freeable(void *ptr);\n"
    // True iff ptr satisfies the preconditions of the free stdlib function
    CPROVER_PREFIX "bool " CPROVER_PREFIX "is_freeable(void *ptr);\n"
    // True iff ptr was freed during function execution or loop execution
    CPROVER_PREFIX "bool " CPROVER_PREFIX "was_freed(void *ptr);\n"
    "\n";
  // clang-format on

  // GCC junk stuff, also for CLANG and ARM
  if(
    config.ansi_c.mode == configt::ansi_ct::flavourt::GCC ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::CLANG ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::ARM)
  {
    code+=gcc_builtin_headers_types;
    if(support_float16_type)
    {
      code +=
        "typedef _Float16 __gcc_v8hf __attribute__((__vector_size__(16)));\n";
      code +=
        "typedef _Float16 __gcc_v16hf __attribute__((__vector_size__(32)));\n";
      code +=
        "typedef _Float16 __gcc_v32hf __attribute__((__vector_size__(64)));\n";
    }

    // there are many more, e.g., look at
    // https://developer.apple.com/library/mac/#documentation/developertools/gcc-4.0.1/gcc/Target-Builtins.html

    if(
      config.ansi_c.arch == "i386" || config.ansi_c.arch == "x86_64" ||
      config.ansi_c.arch == "x32" || config.ansi_c.arch == "ia64" ||
      config.ansi_c.arch == "powerpc" || config.ansi_c.arch == "ppc64")
    {
      // https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
      // For clang, __float128 is a keyword.
      // For gcc, this is a typedef and not a keyword.
      if(
        config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG &&
        config.ansi_c.gcc__float128_type)
      {
        code += "typedef " CPROVER_PREFIX "Float128 __float128;\n";
      }
    }
    else if(config.ansi_c.arch == "ppc64le")
    {
      // https://patchwork.ozlabs.org/patch/792295/
      if(config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG)
        code += "typedef " CPROVER_PREFIX "Float128 __ieee128;\n";
    }
    else if(config.ansi_c.arch == "hppa")
    {
      // https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
      // For clang, __float128 is a keyword.
      // For gcc, this is a typedef and not a keyword.
      if(
        config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG &&
        config.ansi_c.gcc__float128_type)
      {
        code+="typedef long double __float128;\n";
      }
    }

    if(
      config.ansi_c.arch == "i386" || config.ansi_c.arch == "x86_64" ||
      config.ansi_c.arch == "x32" || config.ansi_c.arch == "ia64")
    {
      // clang doesn't do __float80
      // Note that __float80 is a typedef, and not a keyword.
      if(config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG)
        code += "typedef " CPROVER_PREFIX "Float64x __float80;\n";
    }

    // On 64-bit systems, gcc has typedefs
    // __int128_t und __uint128_t -- but not on 32 bit!
    if(config.ansi_c.long_int_width>=64)
    {
      code+="typedef signed __int128 __int128_t;\n"
            "typedef unsigned __int128 __uint128_t;\n";
    }
  }

  // this is Visual C/C++ only
  if(config.ansi_c.os==configt::ansi_ct::ost::OS_WIN)
    code += "int __assume(int);\n";

  // ARM stuff
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::ARM)
    code+=arm_builtin_headers;

  // CW stuff
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::CODEWARRIOR)
    code+=cw_builtin_headers;

  // Architecture strings
  ansi_c_architecture_strings(code);
}

void ansi_c_architecture_strings(std::string &code)
{
  // The following are CPROVER-specific.
  // They allow identifying the architectural settings used
  // at compile time from a goto-binary.

  code += "#line 1 \"<builtin-architecture-strings>\"\n";

  code+=architecture_string(config.ansi_c.int_width, "int_width");
  code+=architecture_string(config.ansi_c.int_width, "word_size"); // old
  code+=architecture_string(config.ansi_c.long_int_width, "long_int_width");
  code+=architecture_string(config.ansi_c.bool_width, "bool_width");
  code+=architecture_string(config.ansi_c.char_width, "char_width");
  code+=architecture_string(config.ansi_c.short_int_width, "short_int_width");
  code+=architecture_string(config.ansi_c.long_long_int_width, "long_long_int_width"); // NOLINT(whitespace/line_length)
  code+=architecture_string(config.ansi_c.pointer_width, "pointer_width");
  code+=architecture_string(config.ansi_c.single_width, "single_width");
  code+=architecture_string(config.ansi_c.double_width, "double_width");
  code+=architecture_string(config.ansi_c.long_double_width, "long_double_width"); // NOLINT(whitespace/line_length)
  code+=architecture_string(config.ansi_c.wchar_t_width, "wchar_t_width");
  code+=architecture_string(config.ansi_c.char_is_unsigned, "char_is_unsigned");
  code+=architecture_string(config.ansi_c.wchar_t_is_unsigned, "wchar_t_is_unsigned"); // NOLINT(whitespace/line_length)
  code+=architecture_string(config.ansi_c.alignment, "alignment");
  code+=architecture_string(config.ansi_c.memory_operand_size, "memory_operand_size"); // NOLINT(whitespace/line_length)
  code+=architecture_string(static_cast<int>(config.ansi_c.endianness), "endianness"); // NOLINT(whitespace/line_length)
  code+=architecture_string(id2string(config.ansi_c.arch), "arch");
  code+=architecture_string(configt::ansi_ct::os_to_string(config.ansi_c.os), "os"); // NOLINT(whitespace/line_length)
  code+=architecture_string(config.ansi_c.NULL_is_zero, "NULL_is_zero");
}
