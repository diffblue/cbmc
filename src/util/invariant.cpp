/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@diffblue.com

\*******************************************************************/


#include "invariant.h"

#include <string>
#include <sstream>

#include <iostream>

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
  const std::string &stack_entry)
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


/// Prints a back trace to 'out'
/// \param out: Stream to print backtrace
void print_backtrace(
  std::ostream &out)
{
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
}

/// Returns a backtrace
/// \return backtrace with a file / function / line header.
std::string get_backtrace()
{
  std::ostringstream ostr;
  print_backtrace(ostr);
  return ostr.str();
}

/// Dump exception report to stderr
void report_exception_to_stderr(const invariant_failedt &reason)
{
  std::cerr << "--- begin invariant violation report ---\n";
  std::cerr << reason.what() << '\n';
  std::cerr << "--- end invariant violation report ---\n";
}

std::string invariant_failedt::get_invariant_failed_message(
  const std::string &file,
  const std::string &function,
  int line,
  const std::string &backtrace,
  const std::string &reason)
{
  std::ostringstream out;
  out << "Invariant check failed\n"
      << "File " << file
      << " function " << function
      << " line " << line << '\n'
      << "Reason: " << reason
      << "\nBacktrace:\n"
      << backtrace << '\n';
  return out.str();
}
