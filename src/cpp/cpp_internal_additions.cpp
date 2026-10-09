/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cpp_internal_additions.h"

#include <util/c_types.h>
#include <util/config.h>

#include <goto-programs/adjust_float_expressions.h>

#include <ansi-c/ansi_c_internal_additions.h>
#include <linking/static_lifetime_init.h>

#include <ostream>

std::string c2cpp(const std::string &s)
{
  std::string result;

  result.reserve(s.size());

  for(std::size_t i = 0; i < s.size(); i++)
  {
    char ch = s[i];

    if(ch == '_' && std::string(s, i, 5) == "_Bool")
    {
      result.append("bool");
      i += 4;
      continue;
    }

    result += ch;
  }

  return result;
}

void cpp_internal_additions(std::ostream &out)
{
  out << "#line 1 \"<built-in-additions>\"" << '\n';

  // __CPROVER namespace
  out << "namespace __CPROVER { }" << '\n';

  // types
  out << "typedef __typeof__(sizeof(int)) __CPROVER::size_t;" << '\n';
  out << "typedef __CPROVER::size_t " CPROVER_PREFIX "size_t;" << '\n';
  out << "typedef " << c_type_as_string(signed_size_type().get(ID_C_c_type))
      << " __CPROVER::ssize_t;" << '\n';
  out << "typedef __CPROVER::ssize_t " CPROVER_PREFIX "ssize_t;" << '\n';

  // new and delete are in the root namespace!
  out << "void operator delete(void *);" << '\n';
  out << "void *operator new(__CPROVER::size_t);" << '\n';

  out << "extern \"C\" {" << '\n';

  // CPROVER extensions
  out << "const unsigned __CPROVER::constant_infinity_uint;" << '\n';
  out << "typedef void " CPROVER_PREFIX "integer;" << '\n';
  out << "typedef void " CPROVER_PREFIX "rational;" << '\n';

  // memory model
  out << "extern unsigned char " CPROVER_PREFIX
      << "memory[__CPROVER::constant_infinity_uint];" << '\n';

  // malloc
  out << "const void *" CPROVER_PREFIX "deallocated = 0;" << '\n';
  out << "const void *" CPROVER_PREFIX "dead_object = 0;" << '\n';
  out << "const void *" CPROVER_PREFIX "memory_leak = 0;" << '\n';
  out << "void *" CPROVER_PREFIX "allocate("
      << CPROVER_PREFIX "size_t size, " CPROVER_PREFIX "bool zero);" << '\n';

  // auxiliaries for new/delete
  out << "void *__new(__CPROVER::size_t);" << '\n';
  out << "void *__new_array(__CPROVER::size_t, __CPROVER::size_t);" << '\n';
  out << "void *__placement_new(__CPROVER::size_t, void *);" << '\n';
  out << "void *__placement_new_array("
      << "__CPROVER::size_t, __CPROVER::size_t, void *);" << '\n';
  out << "void __delete(void *);" << '\n';
  out << "void __delete_array(void *);" << '\n';

  // float
  // TODO: should be thread_local
  out << "int " << rounding_mode_identifier() << " = "
      << std::to_string(config.ansi_c.rounding_mode) << ';' << '\n';

  // pipes, write, read, close
  out << "struct " CPROVER_PREFIX "pipet {\n"
      << "  bool widowed;\n"
      << "  char data[4];\n"
      << "  short next_avail;\n"
      << "  short next_unread;\n"
      << "};\n";

  // This function needs to be declared, or otherwise can't be called
  // by the entry-point construction.
  out << "void " INITIALIZE_FUNCTION "();" << '\n';

  // GCC junk stuff, also for CLANG and ARM
  if(
    config.ansi_c.mode == configt::ansi_ct::flavourt::GCC ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::CLANG ||
    config.ansi_c.mode == configt::ansi_ct::flavourt::ARM)
  {
    out << c2cpp(gcc_builtin_headers_types);

    if(
      config.ansi_c.arch == "i386" || config.ansi_c.arch == "x86_64" ||
      config.ansi_c.arch == "x32" || config.ansi_c.arch == "ia64" ||
      config.ansi_c.arch == "powerpc" || config.ansi_c.arch == "ppc64")
    {
      // https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
      // For clang, __float128 is a keyword.
      // For gcc, this is a typedef and not a keyword.
      // C++ doesn't have _Float128.
      if(config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG)
        out << "typedef " CPROVER_PREFIX "Float128 __float128;" << '\n';
    }
    else if(config.ansi_c.arch == "hppa")
    {
      // https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
      // For clang, __float128 is a keyword.
      // For gcc, this is a typedef and not a keyword.
      // C++ doesn't have _Float128.
      if(config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG)
        out << "typedef long double __float128;" << '\n';
    }
    else if(config.ansi_c.arch == "ppc64le")
    {
      // https://patchwork.ozlabs.org/patch/792295/
      if(config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG)
        out << "typedef " CPROVER_PREFIX "Float128 __ieee128;\n";
    }

    if(
      config.ansi_c.arch == "i386" || config.ansi_c.arch == "x86_64" ||
      config.ansi_c.arch == "x32" || config.ansi_c.arch == "ia64")
    {
      // clang doesn't do __float80
      // Note that __float80 is a typedef, and not a keyword,
      // and that C++ doesn't have _Float64x.
      if(config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG)
        out << "typedef " CPROVER_PREFIX "Float80 __float80;" << '\n';
    }

    // On 64-bit systems, gcc has typedefs
    // __int128_t und __uint128_t -- but not on 32 bit!
    if(config.ansi_c.long_int_width >= 64)
    {
      out << "typedef signed __int128 __int128_t;" << '\n';
      out << "typedef unsigned __int128 __uint128_t;" << '\n';
    }

    if(
      config.ansi_c.arch == "arm64" &&
      config.ansi_c.os != configt::ansi_ct::ost::OS_MACOS)
    {
      out << "typedef struct __va_list {";
      out << "void *__stack;";
      out << "void *__gr_top;";
      out << "void *__vr_top;";
      out << "int   __gr_offs;";
      out << "int   __vr_offs;";
      out << " } __builtin_va_list;" << '\n';
    }
    else
    {
      out << "typedef void ** __builtin_va_list;" << '\n';
    }
  }

  // this is Visual C/C++ only
  if(config.ansi_c.os == configt::ansi_ct::ost::OS_WIN)
  {
    out << "int __noop(...);" << '\n';
    out << "int __assume(int);" << '\n';
  }

  // ARM stuff
  if(config.ansi_c.mode == configt::ansi_ct::flavourt::ARM)
    out << c2cpp(arm_builtin_headers);

  // CW stuff
  if(config.ansi_c.mode == configt::ansi_ct::flavourt::CODEWARRIOR)
    out << c2cpp(cw_builtin_headers);

  // string symbols to identify the architecture we have compiled for
  std::string architecture_strings;
  ansi_c_architecture_strings(architecture_strings);
  out << c2cpp(architecture_strings);

  out << '}' << '\n'; // end extern "C"

  // GCC __builtin_addressof
  out << "template<typename _Tp> _Tp* __builtin_addressof(_Tp& __r)"
         " { return &__r; }\n";

  // Microsoft stuff
  if(config.ansi_c.mode == configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
    // MSVC headers use GCC-style builtins like __builtin_strlen and
    // __builtin_memcmp in their STL implementations.
    out << "extern \"C\" " CPROVER_PREFIX
        << "size_t __builtin_strlen(const char *s)\n"
        << "{ " CPROVER_PREFIX "size_t i=0; while(s[i]!=0) i++; return i; }\n";
    out << "extern \"C\" int __builtin_memcmp"
           "(const void*, const void*, " CPROVER_PREFIX "size_t);\n";
    // type_info infrastructure -- the standard wants this to be in the
    // std:: namespace, but MS has it in the root namespace
    out << "class type_info;" << '\n';

    // this is the return type of __uuidof(...),
    // in the root namespace
    out << "struct _GUID;" << '\n';

    // MS ATL-related stuff
    out << "namespace ATL; " << '\n';
    out << "void ATL::AtlThrowImpl(long);" << '\n';
    out << "void __stdcall ATL::AtlThrowLastWin32();" << '\n';
  }

  // C++20 coroutine builtins (stubs for type-checking)
  out << "void *__builtin_coro_promise(void *, int, bool);\n";
  out << "bool __builtin_coro_done(void *);\n";
  out << "void __builtin_coro_resume(void *);\n";
  out << "void __builtin_coro_destroy(void *);\n";
  out << "void *__builtin_coro_noop();\n";

  // Clang SIMD vector reduction builtins (polymorphic stubs).
  // The actual lowering to element-wise operations is done by
  // typecheck_vector_reduce in c_typecheck_gcc_polymorphic_builtins.cpp.
  out << "template<typename _Tp> _Tp __builtin_reduce_and(_Tp);\n";
  out << "template<typename _Tp> _Tp __builtin_reduce_or(_Tp);\n";
  out << "template<typename _Tp> _Tp __builtin_reduce_xor(_Tp);\n";
  out << "template<typename _Tp> _Tp __builtin_reduce_add(_Tp);\n";
  out << "template<typename _Tp> _Tp __builtin_reduce_mul(_Tp);\n";

  // __builtin_is_constant_evaluated(): provide a run-time definition returning
  // false ([meta.const.eval]/1: false outside constant evaluation).  Calls in
  // a manifestly constant-evaluated context are folded to true in
  // typecheck_side_effect_function_call before this body would be used, so this
  // body is only reached at run time.
  out << "inline bool __builtin_is_constant_evaluated() { return false; }\n";

  // GCC/Clang checked arithmetic builtins
  out << "bool __builtin_add_overflow(...);\n";
  out << "bool __builtin_sub_overflow(...);\n";
  out << "bool __builtin_mul_overflow(...);\n";
  out << "bool __builtin_add_overflow_p(...);\n";
  out << "bool __builtin_sub_overflow_p(...);\n";
  out << "bool __builtin_mul_overflow_p(...);\n";

  // NOTE: earlier versions injected fixed-arity std::__and_/__or_
  // replacements here because CBMC could not evaluate GCC 13's real
  // definitions (decltype + SFINAE over pack expansions).  The front
  // end handles those now, and the injected primary declaration
  // conflicted with the real (and any user) definition of the same
  // name ([basic.def.odr]): template-id resolution could pick the
  // injected arity-limited declaration and silently fail.  Only the
  // __to_address helper remains.
  if(
    config.ansi_c.mode != configt::ansi_ct::flavourt::VISUAL_STUDIO &&
    config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP11)
  {
    // clang-format off
    out <<
      "namespace std {\n"
      "  template<typename _Tp> constexpr _Tp*\n"
      "    __to_address(_Tp* __ptr) { return __ptr; }\n"
      "}\n";
    // clang-format on
  }

  // C++20 std::dynamic_extent — provide as built-in so that
  // <span> can use it as a default template argument without
  // needing to evaluate numeric_limits<size_t>::max().
  if(config.cpp.cpp_standard >= configt::cppt::cpp_standardt::CPP20)
  {
    out << "namespace std {\n";
    out << "  inline constexpr __CPROVER::size_t dynamic_extent = "
           "(__CPROVER::size_t)-1;\n";
    // Also in inline namespace __1 for libc++
    out << "  inline namespace __1 {\n";
    out << "    inline constexpr __CPROVER::size_t dynamic_extent = "
           "(__CPROVER::size_t)-1;\n";
    out << "  }\n";
    out << "}\n";
  }

  out << std::flush;
}
