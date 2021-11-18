/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_internal_additions.h"

#include <util/c_types.h>
#include <util/config.h>

#include <linking/static_lifetime_init.h>

#include <goto-programs/adjust_float_expressions.h>

const char gcc_builtin_headers_types[]=
"# 1 \"gcc_builtin_headers_types.h\"\n"
#include "gcc_builtin_headers_types.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_generic[]=
"# 1 \"gcc_builtin_headers_generic.h\"\n"
#include "gcc_builtin_headers_generic.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_math[]=
"# 1 \"gcc_builtin_headers_math.h\"\n"
#include "gcc_builtin_headers_math.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_mem_string[]=
"# 1 \"gcc_builtin_headers_mem_string.h\"\n"
#include "gcc_builtin_headers_mem_string.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_omp[]=
"# 1 \"gcc_builtin_headers_omp.h\"\n"
#include "gcc_builtin_headers_omp.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_tm[]=
"# 1 \"gcc_builtin_headers_tm.h\"\n"
#include "gcc_builtin_headers_tm.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_ubsan[]=
"# 1 \"gcc_builtin_headers_ubsan.h\"\n"
#include "gcc_builtin_headers_ubsan.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_ia32[]=
"# 1 \"gcc_builtin_headers_ia32.h\"\n"
#include "gcc_builtin_headers_ia32.inc"
; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_2[]=
#include "gcc_builtin_headers_ia32-2.inc"
; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_3[]=
#include "gcc_builtin_headers_ia32-3.inc"
; // NOLINT(whitespace/semicolon)
const char gcc_builtin_headers_ia32_4[]=
#include "gcc_builtin_headers_ia32-4.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_alpha[]=
"# 1 \"gcc_builtin_headers_alpha.h\"\n"
#include "gcc_builtin_headers_alpha.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_arm[]=
"# 1 \"gcc_builtin_headers_arm.h\"\n"
#include "gcc_builtin_headers_arm.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_mips[]=
"# 1 \"gcc_builtin_headers_mips.h\"\n"
#include "gcc_builtin_headers_mips.inc"
; // NOLINT(whitespace/semicolon)

const char gcc_builtin_headers_power[]=
"# 1 \"gcc_builtin_headers_power.h\"\n"
#include "gcc_builtin_headers_power.inc"
; // NOLINT(whitespace/semicolon)

const char arm_builtin_headers[]=
"# 1 \"arm_builtin_headers.h\"\n"
#include "arm_builtin_headers.inc"
; // NOLINT(whitespace/semicolon)

const char cw_builtin_headers[]=
"# 1 \"cw_builtin_headers.h\"\n"
#include "cw_builtin_headers.inc"
; // NOLINT(whitespace/semicolon)

const char clang_builtin_headers[]=
"# 1 \"clang_builtin_headers.h\"\n"
#include "clang_builtin_headers.inc"
; // NOLINT(whitespace/semicolon)

const char cprover_builtin_headers[]=
"# 1 \"cprover_builtin_headers.h\"\n"
#include "cprover_builtin_headers.inc"
; // NOLINT(whitespace/semicolon)

const char windows_builtin_headers[]=
"# 1 \"windows_builtin_headers.h\"\n"
#include "windows_builtin_headers.inc"
; // NOLINT(whitespace/semicolon)

static std::string architecture_string(const std::string &value, const char *s)
{
  return std::string("const char *" CPROVER_PREFIX "architecture_") +
         std::string(s) + "=\"" + value + "\";\n";
}

template <typename T>
static std::string architecture_string(T value, const char *s)
{
  return std::string("const int " CPROVER_PREFIX "architecture_") +
         std::string(s) + "=" + std::to_string(value) + ";\n";
}

/// The maximum allocation size is determined by the number of bits that
/// are left in the pointer of width \p pointer_width.
///
/// The allocation size cannot exceed the number represented by the (signed)
/// offset, otherwise it would not be possible to store a pointer into a
/// valid bit of memory. Therefore, the max allocation size is
/// 2^(offset_bits - 1), where the offset bits is the number of bits left in the
/// pointer after the object bits.
///
/// The offset must be signed, as a pointer can point to the end of the memory
/// block, and needs to be able to point back to the start.
/// \param pointer_width: The width of the pointer
/// \param object_bits : The number of bits used to represent the ID
/// \return The size in bytes of the maximum allocation supported.
static mp_integer
max_malloc_size(std::size_t pointer_width, std::size_t object_bits)
{
  PRECONDITION(pointer_width >= 1);
  PRECONDITION(object_bits < pointer_width);
  PRECONDITION(object_bits >= 1);
  const auto offset_bits = pointer_width - object_bits;
  // We require the offset to be able to express upto allocation_size - 1,
  // but also down to -allocation_size, therefore the size is allowable
  // is number of bits, less the signed bit.
  const auto bits_for_positive_offset = offset_bits - 1;
  return ((mp_integer)1) << (mp_integer)bits_for_positive_offset;
}

void ansi_c_internal_additions(std::string &code)
{
  // clang-format off
  // do the built-in types and variables
  code+=
    "# 1 \"<built-in-additions>\"\n"
    "typedef __typeof__(sizeof(int)) " CPROVER_PREFIX "size_t;\n"
    "typedef "+c_type_as_string(signed_size_type().get(ID_C_c_type))+
      " " CPROVER_PREFIX "ssize_t;\n"
    "const unsigned " CPROVER_PREFIX "constant_infinity_uint;\n"
    "typedef void " CPROVER_PREFIX "integer;\n"
    "typedef void " CPROVER_PREFIX "rational;\n"
    CPROVER_PREFIX "thread_local unsigned long " CPROVER_PREFIX "thread_id=0;\n"
    CPROVER_PREFIX "bool " CPROVER_PREFIX "threads_exited["
      CPROVER_PREFIX "constant_infinity_uint];\n"
    "unsigned long " CPROVER_PREFIX "next_thread_id=0;\n"
    CPROVER_PREFIX "thread_local const void* " CPROVER_PREFIX "thread_keys["
      CPROVER_PREFIX "constant_infinity_uint];\n"
    CPROVER_PREFIX "thread_local void (*" CPROVER_PREFIX "thread_key_dtors["
      CPROVER_PREFIX "constant_infinity_uint])(void *);\n"
    CPROVER_PREFIX "thread_local unsigned long "
      CPROVER_PREFIX "next_thread_key = 0;\n"
    "extern unsigned char " CPROVER_PREFIX "memory["
      CPROVER_PREFIX "constant_infinity_uint];\n"

    // malloc
    "const void *" CPROVER_PREFIX "deallocated=0;\n"
    "const void *" CPROVER_PREFIX "dead_object=0;\n"
    "const void *" CPROVER_PREFIX "new_object=0;\n" // for C++
    CPROVER_PREFIX "bool " CPROVER_PREFIX "malloc_is_new_array=0;\n" // for C++
    "const void *" CPROVER_PREFIX "memory_leak=0;\n"
    "void *" CPROVER_PREFIX "allocate("
      CPROVER_PREFIX "size_t size, " CPROVER_PREFIX "bool zero);\n"
    "const void *" CPROVER_PREFIX "alloca_object = 0;\n"

    "extern int " CPROVER_PREFIX "malloc_failure_mode;\n"
    "int " CPROVER_PREFIX "malloc_failure_mode_return_null="+
    std::to_string(config.ansi_c.malloc_failure_mode_return_null)+";\n"
    "int " CPROVER_PREFIX "malloc_failure_mode_assert_then_assume="+
    std::to_string(config.ansi_c.malloc_failure_mode_assert_then_assume)+";\n"
    CPROVER_PREFIX "size_t " CPROVER_PREFIX "max_malloc_size="+
    integer2string(max_malloc_size(config.ansi_c.pointer_width, config
    .bv_encoding.object_bits))+";\n"
    "extern " CPROVER_PREFIX "bool " CPROVER_PREFIX "malloc_may_fail;\n"

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
    "extern struct " CPROVER_PREFIX "pipet " CPROVER_PREFIX "pipes["
      CPROVER_PREFIX "constant_infinity_uint];\n"
    // offset to make sure we don't collide with other fds
    "extern const int " CPROVER_PREFIX "pipe_offset;\n"
    "unsigned " CPROVER_PREFIX "pipe_count=0;\n"
    "\n"
    // This function needs to be declared, or otherwise can't be called
    // by the entry-point construction.
    "void " INITIALIZE_FUNCTION "(void);\n"
    "\n";
  // clang-format on

  // GCC junk stuff, also for CLANG and ARM
  if(
    config.ansi_c.mode == configt::ansi_ct::flavourt::GCC ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::CLANG ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::ARM)
  {
    code+=gcc_builtin_headers_types;

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

  code+="# 1 \"<builtin-architecture-strings>\"\n";

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
