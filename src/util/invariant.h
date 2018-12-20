/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_INVARIANT_H
#define CPROVER_UTIL_INVARIANT_H

#include <cstdlib>
#include <sstream>
#include <stdexcept>
#include <string>
#include <type_traits>

/*
** Invariants document conditions that the programmer believes to
** be always true as a consequence of the system architecture and / or
** preceeding code.  In principle it should be possible to (machine
** checked) verify them.  The condition should be side-effect free and
** evaluate to a boolean.
**
** As well as the condition they have a text argument that should be
** used to say why they are true.  The reason should be a string literal
** starting with a lower case character.
** Longer diagnostics should be output to error(). For example:
**
** INVARIANT(
**   x > 0,
**   "x should have a positive value as others are handled by other branches");
**
** Use "should" style statements for messages in invariants (also see
** CODING_STANDARD.md). An example would be "array should have a non-zero size")
** to make both the violation and the expected behavior clear. (As opposed to
** "no zero size arrays" where it isn't clear if the zero-size array is the
** problem, or the lack of it).
**
** To help classify different kinds of invariants, various short-hand
** macros are provided.
**
** Invariants are used to document and check design / implementation
** knowledge.  They should *not* be used:
**  - to validate user input or options
**    (throw an exception or handle more gracefully)
**  - to log information (use debug(), progress(), etc.)
**  - as TODO notes (acceptable in private repositories but fix before PR)
**  - to handle cases that are unlikely, tedious or expensive (ditto)
**  - to modify the state of the system (i.e. no side effects)
**
** Invariants provide the following guarantee:
**  IF the condition is false
**  THEN an invariant_failed exception will be thrown
**       OR there will be undefined behaviour
**
** Consequentally, programmers may assume that the condition of an
** invariant is true after it has been executed.  Applications are
** encouraged to (at least) catch exceptions at the top level and
** output them.
**
** Various different approaches to checking (or not) the invariants
** and handling their failure are supported and can be configured with
** CPROVER_INVARIANT_* macros.
*/

/// A logic error, augmented with a distinguished field to hold a backtrace.
/// Classes that extend this one should share the same initial constructor
/// parameters: their constructor signature should be of the form:
/// my_invariantt::my_invariantt(
///   const std::string &file,
///   const std::string &function,
///   int line,
///   const std::string &backtrace,
///   T1 arg1,
///   T2 arg2 ...
///   Tn argn)
/// It should pretty-print the T1 ... Tn arguments and pass it as `reason` to
/// invariant_failedt's constructor, or else simply pass a reason string
/// through.
/// Conforming to this pattern allows the class to be used with the INVARIANT
/// family of macros, allowing constructs like
/// `INVARIANT(x==y, my_invariantt, (T1)actual1, (T2)actual2, ...)`
///
/// \ref invariant_failedt is also the base class of any 'structured
/// exceptions' - as found in file \ref base_exceptions.h
///
class invariant_failedt
{
 private:
  const std::string file;
  const std::string function;
  const int line;
  const std::string backtrace;
  const std::string condition;
  const std::string reason;

public:
  virtual ~invariant_failedt() = default;

  virtual std::string what() const noexcept;

  invariant_failedt(
    const std::string &_file,
    const std::string &_function,
    int _line,
    const std::string &_backtrace,
    const std::string &_condition,
    const std::string &_reason)
    : file(_file),
      function(_function),
      line(_line),
      backtrace(_backtrace),
      condition(_condition),
      reason(_reason)
  {
  }
};

/// A class that includes diagnostic information related to an invariant
/// violation.
class invariant_with_diagnostics_failedt : public invariant_failedt
{
private:
  const std::string diagnostics;

public:
  virtual std::string what() const noexcept;

  invariant_with_diagnostics_failedt(
    const std::string &_file,
    const std::string &_function,
    int _line,
    const std::string &_backtrace,
    const std::string &_condition,
    const std::string &_reason,
    const std::string &_diagnostics)
    : invariant_failedt(
        _file,
        _function,
        _line,
        _backtrace,
        _condition,
        _reason),
      diagnostics(_diagnostics)
  {
  }
};

#ifdef __GNUC__
#define CBMC_NORETURN __attribute((noreturn))
#elif defined(_MSC_VER)
#define CBMC_NORETURN __declspec(noreturn)
#elif __cplusplus >= 201703L
#define CBMC_NORETURN [[noreturn]]
#else
#define CBMC_NORETURN
#endif

#if defined(CPROVER_INVARIANT_CPROVER_ASSERT)
// Used to allow CPROVER to check itself
#define INVARIANT(CONDITION, REASON)                                          \
  __CPROVER_assert((CONDITION), "Invariant : " REASON)
#define INVARIANT_WITH_DIAGNOSTICS(CONDITION, REASON, ...)                             \
  __CPROVER_assert((CONDITION), "Invariant : " REASON)

#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...) \
  INVARIANT(CONDITION, "")

#elif defined(CPROVER_INVARIANT_DO_NOT_CHECK)
// For performance builds, invariants can be ignored
// This is *not* recommended as it can result in unpredictable behaviour
// including silently reporting incorrect results.
// This is also useful for checking side-effect freedom.
#define INVARIANT(CONDITION, REASON)                                          \
  do                                                                           \
  {                                                                            \
  } while(false)
#define INVARIANT_WITH_DIAGNOSTICS(CONDITION, REASON, ...)                             \
  do                                                                           \
  {                                                                            \
  } while(false)
#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...) do {} while(false)

#elif defined(CPROVER_INVARIANT_ASSERT)
// Not recommended but provided for backwards compatability
#include <cassert>
// NOLINTNEXTLINE(*)
#define INVARIANT(CONDITION, REASON) assert((CONDITION) && ((REASON), true))
#define INVARIANT_WITH_DIAGNOSTICS(CONDITION, REASON, ...)                             \
  assert((CONDITION) && ((REASON), true)) /* NOLINT */
// NOLINTNEXTLINE(*)
#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...) assert((CONDITION))
#else

void print_backtrace(std::ostream &out);

std::string get_backtrace();

void report_exception_to_stderr(const invariant_failedt &);

/// This function is the backbone of all the invariant types.
/// Every instance of an invariant is ultimately generated by this
/// function template, which is at times called via a wrapper function.
/// Takes a backtrace, gives it to the reason structure, then aborts, printing
/// reason.what() (which therefore includes the backtrace).
/// In future this may throw `reason` instead of aborting.
/// Template parameter ET: type of exception to construct
/// \param file : C string giving the name of the file.
/// \param function : C string giving the name of the function.
/// \param line : The line number of the invariant
/// \param condition : the condition this invariant is checking.
/// \param params : (variadic) parameters to forward to ET's constructor
///  its backtrace member will be set before it is used.
template <class ET, typename... Params>
CBMC_NORETURN
  typename std::enable_if<std::is_base_of<invariant_failedt, ET>::value>::type
  invariant_violated_structured(
    const std::string &file,
    const std::string &function,
    const int line,
    const std::string &condition,
    Params &&... params)
{
  std::string backtrace=get_backtrace();
  ET to_throw(
    file,
    function,
    line,
    backtrace,
    condition,
    std::forward<Params>(params)...);
  // We now have a structured exception ready to use;
  // in future this is the place to put a 'throw'.
  report_exception_to_stderr(to_throw);
  abort();
}

/// This is a wrapper function used by the macro 'INVARIANT(CONDITION, REASON)'.
/// It constructs an invariant_violatedt from reason and the
/// backtrace, then aborts after printing the invariant's description.
/// In future this may throw rather than aborting.
/// \param file : C string giving the name of the file.
/// \param function : C string giving the name of the function.
/// \param line : The line number of the invariant
/// \param reason : brief description of the invariant violation.
/// \param condition : the condition this invariant is checking.
CBMC_NORETURN
inline void
invariant_violated_string(
  const std::string &file,
  const std::string &function,
  const int line,
  const std::string &condition,
  const std::string &reason)
{
  invariant_violated_structured<invariant_failedt>(
    file, function, line, condition, reason);
}

namespace detail
{
template <typename T>
struct always_falset : public std::false_type
{
};
} // namespace detail

/// Helper to give us some diagnostic in a usable form on assertion failure.
/// For now only provides string output
/// Must be specialised for all types that should be useable as diagnostics
template <typename T>
struct diagnostics_helpert
{
  // silly construct because C++ won't let us write static_assert(false,...)
  static_assert(
    detail::always_falset<T>::value,
    "to avoid unintended strangeness, diagnostics_helpert needs to be "
    "specialised for each diagnostic type");
  static std::string diagnostics_as_string(const T &);
};

// Standard string specialisations for diagnostics_helper
// (character arrays, character pointers and std::string)

template <std::size_t N>
struct diagnostics_helpert<char[N]>
{
  static std::string diagnostics_as_string(const char (&string)[N])
  {
    return string;
  }
};
template <>
struct diagnostics_helpert<char *>
{
  static std::string diagnostics_as_string(const char *string)
  {
    return string;
  }
};

template <>
struct diagnostics_helpert<std::string>
{
  // This is deliberately taking a copy instead of a reference
  // to avoid making an extra copy when passing a temporary string
  // as a diagnostic
  static std::string diagnostics_as_string(std::string string)
  {
    return string;
  }
};

namespace detail
{
inline std::string assemble_diagnostics()
{
  return "";
}

template <typename T>
std::string diagnostic_as_string(T &&val)
{
  return diagnostics_helpert<
    typename std::remove_cv<typename std::remove_reference<T>::type>::type>::
    diagnostics_as_string(std::forward<T>(val));
}

inline void write_rest_diagnostics(std::ostream &)
{
}

template <typename T, typename... Ts>
void write_rest_diagnostics(std::ostream &out, T &&next, Ts &&... rest)
{
  out << "\n" << diagnostic_as_string(std::forward<T>(next));
  write_rest_diagnostics(out, std::forward<Ts>(rest)...);
}

template <typename... Diagnostics>
std::string assemble_diagnostics(Diagnostics &&... args)
{
  std::ostringstream out;
  out << "\n<< EXTRA DIAGNOSTICS >>";
  write_rest_diagnostics(out, std::forward<Diagnostics>(args)...);
  out << "\n<< END EXTRA DIAGNOSTICS >>";
  return out.str();
}
} // namespace detail

/// This is a wrapper function, used by the macro 'INVARIANT_WITH_DIAGNOSTICS'
template <typename... Diagnostics>
CBMC_NORETURN void report_invariant_failure(
  const std::string &file,
  const std::string &function,
  int line,
  std::string reason,
  std::string condition,
  Diagnostics &&... diagnostics)
{
  invariant_violated_structured<invariant_with_diagnostics_failedt>(
    file,
    function,
    line,
    reason,
    condition,
    detail::assemble_diagnostics(std::forward<Diagnostics>(diagnostics)...));
}

#define EXPAND_MACRO(x) x

// These require a trailing semicolon by the user, such that INVARIANT
// behaves syntactically like a function call.
// NOLINT as macro definitions confuse the linter it seems.
#ifdef _MSC_VER
#define CURRENT_FUNCTION_NAME __FUNCTION__
#else
#define CURRENT_FUNCTION_NAME __func__
#endif

#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...)                         \
  do /* NOLINT */                                                              \
  {                                                                            \
    if(!(CONDITION))                                                           \
      invariant_violated_structured<TYPENAME>(                                 \
        __FILE__,                                                              \
        CURRENT_FUNCTION_NAME,                                                 \
        __LINE__,                                                              \
        #CONDITION,                                                            \
        __VA_ARGS__); /* NOLINT */                                             \
  } while(false)

// Short hand macros. The variants *_STRUCTURED below allow to specify a custom
// exception, and are equivalent to INVARIANT_STRUCTURED.

/// This macro uses the wrapper function 'invariant_violated_string'.
#define INVARIANT(CONDITION, REASON)                                           \
  do                                                                           \
  {                                                                            \
    if(!(CONDITION))                                                           \
    {                                                                          \
      invariant_violated_string(                                               \
        __FILE__, CURRENT_FUNCTION_NAME, __LINE__, #CONDITION, REASON);        \
    }                                                                          \
  } while(false)

/// Same as invariant, with one or more diagnostics attached
/// Diagnostics can be of any type that has a specialisation for
/// invariant_helpert
/// This macro uses the wrapper function 'report_invariant_failure'.
#define INVARIANT_WITH_DIAGNOSTICS(CONDITION, REASON, ...)                     \
  do                                                                           \
  {                                                                            \
    if(!(CONDITION))                                                           \
    {                                                                          \
      report_invariant_failure(                                                \
        __FILE__,                                                              \
        CURRENT_FUNCTION_NAME,                                                 \
        __LINE__,                                                              \
        REASON,                                                                \
        #CONDITION,                                                            \
        __VA_ARGS__);                                                          \
    }                                                                          \
  } while(false)

#endif // End CPROVER_DO_NOT_CHECK / CPROVER_ASSERT / ... if block

// The condition should only contain (unmodified) inputs to the method. Inputs
// include arguments passed to the function, as well as member variables that
// the function may read.
// "The design of the system means that the arguments to this method
//  will always meet this condition".
//
// The PRECONDITION documents / checks assumptions about the inputs
// that is the caller's responsibility to make happen before the call.

#define PRECONDITION(CONDITION) INVARIANT(CONDITION, "Precondition")
#define PRECONDITION_WITH_DIAGNOSTICS(CONDITION, ...)                          \
  INVARIANT_WITH_DIAGNOSTICS(CONDITION, "Precondition", __VA_ARGS__)

#define PRECONDITION_STRUCTURED(CONDITION, TYPENAME, ...)                      \
  EXPAND_MACRO(INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__))

// The condition should only contain variables that will be returned /
// output without further modification.
// "The implementation of this method means that the condition will hold".
//
// A POSTCONDITION documents what the function can guarantee about its
// output when it returns, given that it was called with valid inputs.
// Outputs include the return value of the function, as well as member
// variables that the function may write.

#define POSTCONDITION(CONDITION) INVARIANT(CONDITION, "Postcondition")
#define POSTCONDITION_WITH_DIAGNOSTICS(CONDITION, ...)                         \
  INVARIANT_WITH_DIAGNOSTICS(CONDITION, "Postcondition", __VA_ARGS__)

#define POSTCONDITION_STRUCTURED(CONDITION, TYPENAME, ...)                     \
  EXPAND_MACRO(INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__))

// The condition should only contain (unmodified) values that were
// changed by a previous method call.
// "The contract of the previous method call means the following
//  condition holds".
//
// A difference between CHECK_RETURN and POSTCONDITION is that CHECK_RETURN is
// a statement about what the caller expects from a function, whereas a
// POSTCONDITION is a statement about guarantees made by the function itself.

#define CHECK_RETURN(CONDITION) INVARIANT(CONDITION, "Check return value")
#define CHECK_RETURN_WITH_DIAGNOSTICS(CONDITION, ...)                          \
  INVARIANT_WITH_DIAGNOSTICS(CONDITION, "Check return value", __VA_ARGS__)

#define CHECK_RETURN_STRUCTURED(CONDITION, TYPENAME, ...)                      \
  EXPAND_MACRO(INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__))

/// This should be used to mark dead code
#define UNREACHABLE INVARIANT(false, "Unreachable")
#define UNREACHABLE_STRUCTURED(TYPENAME, ...)                                  \
  EXPAND_MACRO(INVARIANT_STRUCTURED(false, TYPENAME, __VA_ARGS__))

/// This condition should be used to document that assumptions that are
/// made on goto_functions, goto_programs, exprts, etc. being well formed.
/// "The data structure is not corrupt or malformed"
#define DATA_INVARIANT(CONDITION, REASON) INVARIANT(CONDITION, REASON)
#define DATA_INVARIANT_WITH_DIAGNOSTICS(CONDITION, REASON, ...)                \
  INVARIANT_WITH_DIAGNOSTICS(CONDITION, REASON, __VA_ARGS__)

#define DATA_INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...)                    \
  EXPAND_MACRO(INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__))

// Legacy annotations

// The following should not be used in new code and are only intended
// to migrate documentation and "error handling" in older code.
#define TODO INVARIANT(false, "Todo")
#define UNIMPLEMENTED INVARIANT(false, "Unimplemented")
#define UNHANDLED_CASE INVARIANT(false, "Unhandled case")

#endif // CPROVER_UTIL_INVARIANT_H
