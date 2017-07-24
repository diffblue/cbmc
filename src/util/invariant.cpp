/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@diffblue.com

\*******************************************************************/


#include "invariant.h"

#include <string>
#include <sstream>

#ifdef CPROVER_INVARIANT_PRINT_STACK_TRACE
#include <iostream>
#include <cstdlib>
#endif

// Backtraces compiler and C library specific
// So we should include something explicitly from the C library
// to check if the C library is glibc.
#include <assert.h>
#ifdef __GLIBC__

// GCC needs LINKFLAGS="-rdynamic" to give function names in the backtrace
#include <execinfo.h>
#include <cxxabi.h>


/// Attempts to demangle the function name assuming the glibc
/// format of stack entry:
///
/// path '(' mangled_name '+' offset ') [' address ']\0'
///
/// \param out: The output stream
/// \param stack_entry: Description of the stack_entry
///
/// \return True <=> the entry has been successfully demangled and printed.
static bool output_demangled_name(
  std::ostream &out,
  const char * const stack_entry)
{
  bool return_value=false;

  std::string working(stack_entry);

  std::string::size_type start=working.rfind('(');  // Path may contain '(' !
  std::string::size_type end=working.find('+', start);

  if(start!=std::string::npos &&
     end!=std::string::npos &&
     start+1<=end-1)
  {
    std::string::size_type length=end-(start+1);
    std::string mangled(working.substr(start+1, length));

    int demangle_success=1;
    char *demangled=
      abi::__cxa_demangle(mangled.c_str(), nullptr, nullptr, &demangle_success);

    if(demangle_success==0)
    {
      out << working.substr(0, start+1)
          << demangled
          << working.substr(end);
      return_value=true;
    }

    free(demangled);
  }

  return return_value;
}
#endif


/// Checks that the given invariant condition holds and prints a back trace
/// and / or throws an exception depending on build configuration.
/// Does not return if condition is false.
/// Returns with no output or state change if true.
///
/// \param file : C string giving the name of the file.
/// \param function : C string giving the name of the function.
/// \param line : The line number of the invariant
/// \param condition : The result of evaluating the invariant condition.
/// \param reason : C string giving the reason why the invariant should be true.
void check_invariant(
  const char * const file,
  const char * const function,
  const int line,
  const bool condition,
  const char * const reason)
{
  if(condition)
    return;

#ifdef CPROVER_INVARIANT_PRINT_STACK_TRACE
    std::ostream & out(std::cerr);
#else
    std::ostringstream out;
#endif

    // Flush regularly so that errors during output will result in
    // partial error logs rather than nothing
    out << "Invariant check failed\n" << std::flush;
    out << "File " << file
        << " function " << function
        << " line " << line
        << '\n' << std::flush;

#ifdef __GLIBC__
    out << "Backtrace\n" << std::flush;

    void * stack[50] = {};

    std::size_t entries=backtrace(stack, sizeof(stack) / sizeof(void *));
    char **description=backtrace_symbols(stack, entries);

    for(std::size_t i=0; i<entries; i++)
    {
      if(!output_demangled_name(out, description[i]))
        out << description[i];
      out << '\n' << std::flush;
    }

    free(description);

#else
    out << "Backtraces not supported\n" << std::flush;
#endif


#ifdef CPROVER_INVARIANT_PRINT_STACK_TRACE
    abort();
#else
    throw invariant_failedt(out.str());
#endif
}
