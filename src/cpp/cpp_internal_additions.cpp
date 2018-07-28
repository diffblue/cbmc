/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "cpp_internal_additions.h"

#include <ostream>

#include <util/c_types.h>
#include <util/config.h>

#include <ansi-c/ansi_c_internal_additions.h>

#include <linking/static_lifetime_init.h>

std::string c2cpp(const std::string &s)
{
  std::string result;

  result.reserve(s.size());

  for(std::size_t i=0; i<s.size(); i++)
  {
    char ch=s[i];

    if(ch=='_' && std::string(s, i, 5)=="_Bool")
    {
      result.append("bool");
      i+=4;
      continue;
    }

    result+=ch;
  }

  return result;
}

void cpp_internal_additions(std::ostream &out)
{
  out << "# 1 \"<built-in-additions>\"" << '\n';

  // __CPROVER namespace
  out << "namespace __CPROVER { }" << '\n';

  // types
  out << "typedef __typeof__(sizeof(int)) __CPROVER::size_t;" << '\n';
  out << "typedef __CPROVER::size_t __CPROVER_size_t;" << '\n';
  out << "typedef "
      << c_type_as_string(signed_size_type().get(ID_C_c_type))
      << " __CPROVER::ssize_t;" << '\n';
  out << "typedef __CPROVER::ssize_t __CPROVER_ssize_t;" << '\n';

  // new and delete are in the root namespace!
  out << "void operator delete(void *);" << '\n';
  out << "void *operator new(__CPROVER::size_t);" << '\n';

  out << "extern \"C\" {" << '\n';

  // CPROVER extensions
  out << "const unsigned __CPROVER::constant_infinity_uint;" << '\n';
  out << "typedef void __CPROVER_integer;" << '\n';
  out << "typedef void __CPROVER_rational;" << '\n';
  // TODO
  // out << "thread_local unsigned long __CPROVER_thread_id = 0;" << '\n';
  out << "__CPROVER_bool "
      << "__CPROVER_threads_exited[__CPROVER::constant_infinity_uint];" << '\n';
  out << "unsigned long __CPROVER_next_thread_id = 0;" << '\n';
  out << "extern unsigned char "
      << "__CPROVER_memory[__CPROVER::constant_infinity_uint];" << '\n';

  // malloc
  out << "const void *__CPROVER_deallocated = 0;" << '\n';
  out << "const void *__CPROVER_dead_object = 0;" << '\n';
  out << "const void *__CPROVER_malloc_object = 0;" << '\n';
  out << "__CPROVER::size_t __CPROVER_malloc_size;" << '\n';
  out << "__CPROVER_bool __CPROVER_malloc_is_new_array = 0;" << '\n';
  out << "const void *__CPROVER_memory_leak = 0;" << '\n';
  out << "void *__CPROVER_allocate(__CPROVER_size_t size, __CPROVER_bool zero);"
      << '\n';

  // auxiliaries for new/delete
  out << "void *__new(__CPROVER::size_t);" << '\n';
  out << "void *__new_array(__CPROVER::size_t, __CPROVER::size_t);" << '\n';
  out << "void *__placement_new(__CPROVER::size_t, void *);" << '\n';
  out << "void *__placement_new_array("
      << "__CPROVER::size_t, __CPROVER::size_t, void *);" << '\n';
  out << "void __delete(void *);" << '\n';
  out << "void __delete_array(void *);" << '\n';

  // float
  // TODO: should the thread_local
  out << "int __CPROVER_rounding_mode = "
      << std::to_string(config.ansi_c.rounding_mode) << ';' << '\n';

  // pipes, write, read, close
  out << "struct __CPROVER_pipet {\n"
      << "  bool widowed;\n"
      << "  char data[4];\n"
      << "  short next_avail;\n"
      << "  short next_unread;\n"
      << "};\n";
  out << "extern struct __CPROVER_pipet "
      << "__CPROVER_pipes[__CPROVER::constant_infinity_uint];" << '\n';
  // offset to make sure we don't collide with other fds
  out << "extern const int __CPROVER_pipe_offset;" << '\n';
  out << "unsigned __CPROVER_pipe_count=0;" << '\n';

  // This function needs to be declared, or otherwise can't be called
  // by the entry-point construction.
  out << "void " INITIALIZE_FUNCTION "();" << '\n';

  // GCC junk stuff, also for CLANG and ARM
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::GCC ||
     config.ansi_c.mode==configt::ansi_ct::flavourt::APPLE ||
     config.ansi_c.mode==configt::ansi_ct::flavourt::ARM)
  {
    out << c2cpp(gcc_builtin_headers_types);

    if(
      config.ansi_c.arch == "i386" || config.ansi_c.arch == "x86_64" ||
      config.ansi_c.arch == "x32")
    {
      // clang doesn't do __float128
      if(config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG)
        out << "typedef double __float128;" << '\n';
    }

    if(
      config.ansi_c.arch == "i386" || config.ansi_c.arch == "x86_64" ||
      config.ansi_c.arch == "x32" || config.ansi_c.arch == "ia64")
    {
      // clang doesn't do __float80
      // Note that __float80 is a typedef, and not a keyword.
      if(config.ansi_c.mode != configt::ansi_ct::flavourt::CLANG)
        out << "typedef __CPROVER_Float64x __float80;" << '\n';
    }

    // On 64-bit systems, gcc has typedefs
    // __int128_t und __uint128_t -- but not on 32 bit!
    if(config.ansi_c.long_int_width >= 64)
    {
      out << "typedef signed __int128 __int128_t;" << '\n';
      out << "typedef unsigned __int128 __uint128_t;" << '\n';
    }
  }

  // this is Visual C/C++ only
  if(config.ansi_c.os==configt::ansi_ct::ost::OS_WIN)
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

  // Microsoft stuff
  if(config.ansi_c.mode==configt::ansi_ct::flavourt::VISUAL_STUDIO)
  {
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

  out << std::flush;
}
