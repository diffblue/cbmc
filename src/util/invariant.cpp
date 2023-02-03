/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@diffblue.com

\*******************************************************************/

#include "invariant.h"

#include "freer.h"

#include <memory>
#include <sstream>
#include <string>

#include <iostream>

#ifdef _WIN32
// the ordering of includes is required
// clang-format off
#include <iomanip>
#include <windows.h>
#include <dbghelp.h>
// clang-format on
#endif

bool cbmc_invariants_should_throw = false;

// Backtraces compiler and C library specific
// So we should include something explicitly from the C library
// to check if the C library is glibc.
#include <assert.h> // IWYU pragma: keep
#if defined(__GLIBC__) || defined(__APPLE__)

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
    std::unique_ptr<char, freert> demangled(
      abi::__cxa_demangle(
        mangled.c_str(), nullptr, nullptr, &demangle_success));

    if(demangle_success==0)
    {
      out << working.substr(0, start+1)
          << demangled.get()
          << working.substr(end);
      return_value=true;
    }
  }

  return return_value;
}
#endif


/// Prints a back trace to 'out'
/// \param out: Stream to print backtrace
void print_backtrace(
  std::ostream &out)
{
#if defined(__GLIBC__) || defined(__APPLE__)
    void * stack[50] = {};

    std::size_t entries=backtrace(stack, sizeof(stack) / sizeof(void *));
    std::unique_ptr<char*, freert> description(
      backtrace_symbols(stack, entries));

    for(std::size_t i=0; i<entries; i++)
    {
      if(!output_demangled_name(out, description.get()[i]))
        out << description.get()[i];
      out << '\n' << std::flush;
    }

#elif defined(_WIN32)

  void *stack[50];
  HANDLE process = GetCurrentProcess();

  SymInitialize(process, NULL, TRUE);

  auto number_of_frames =
    CaptureStackBackTrace(0, sizeof(stack) / sizeof(void *), stack, NULL);

  // Read
  // https://docs.microsoft.com/en-us/windows/win32/api/dbghelp/ns-dbghelp-symbol_info
  // for the rationale behind the size of 'symbol'
  const auto max_name_len = 255;
  auto symbol = static_cast<SYMBOL_INFO *>(
    calloc(sizeof SYMBOL_INFO + (max_name_len - 1) * sizeof(TCHAR), 1));
  symbol->MaxNameLen = max_name_len;
  symbol->SizeOfStruct = sizeof SYMBOL_INFO;

  for(std::size_t i = 0; i < number_of_frames; i++)
  {
    SymFromAddr(process, (DWORD64)(stack[i]), 0, symbol);
    out << std::setw(3) << i;
    out << " 0x" << std::hex << std::setw(8) << symbol->Address;
    out << ' ' << symbol->Name;
    out << '\n' << std::flush;
  }

  free(symbol);
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

std::string invariant_failedt::what() const noexcept
{
  std::ostringstream out;
  out << "Invariant check failed\n"
      << "File: " << file << ":" << line << " function: " << function << '\n'
      << "Condition: " << condition << '\n'
      << "Reason: " << reason << '\n'
      << "Backtrace:" << '\n'
      << backtrace << '\n';
  return out.str();
}

std::string invariant_with_diagnostics_failedt::what() const noexcept
{
  std::string s(invariant_failedt::what());

  if(!s.empty() && s.back() != '\n')
    s += '\n';

  return s + "Diagnostics: " + diagnostics + '\n';
}
