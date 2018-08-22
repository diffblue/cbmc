/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_INVARIANT_H
#define CPROVER_UTIL_INVARIANT_H

#include <cstdlib>
#include <stdexcept>
#include <string>
#include <tuple>
#include <type_traits>

/*
** Invariants document conditions that the programmer believes to
** be always true as a consequence of the system architecture and / or
** preceeding code.  In principle it should be possible to (machine
** checked) verify them.  The condition should be side-effect free and
** evaluate to a boolean.
**
** As well as the condition they have a text argument that should be
** used to say why they are true.  The reason should be a string literals.
** Longer diagnostics should be output to error(). For example:
**
** INVARIANT(x > 0, "x negative and zero case handled by other branches");
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

// The macros MACRO<n> (e.g., INVARIANT2) are for internal use in this file
// only. The corresponding macros that take a variable number of arguments (see
// further below) should be used instead, which in turn call those with a fixed
// number of arguments. For example, if INVARIANT(...) is called with two
// arguments, it calls INVARIANT2().

#if defined(CPROVER_INVARIANT_CPROVER_ASSERT)
// Used to allow CPROVER to check itself
#define INVARIANT2(CONDITION, REASON)                                          \
  __CPROVER_assert((CONDITION), "Invariant : " REASON)
#define INVARIANT3(CONDITION, REASON, DIAGNOSTICS)                             \
  __CPROVER_assert((CONDITION), "Invariant : " REASON)

#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...) \
  INVARIANT(CONDITION, "")

#elif defined(CPROVER_INVARIANT_DO_NOT_CHECK)
// For performance builds, invariants can be ignored
// This is *not* recommended as it can result in unpredictable behaviour
// including silently reporting incorrect results.
// This is also useful for checking side-effect freedom.
#define INVARIANT2(CONDITION, REASON)                                          \
  do                                                                           \
  {                                                                            \
  } while(false)
#define INVARIANT3(CONDITION, REASON, DIAGNOSTICS)                             \
  do                                                                           \
  {                                                                            \
  } while(false)
#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...) do {} while(false)

#elif defined(CPROVER_INVARIANT_ASSERT)
// Not recommended but provided for backwards compatability
#include <cassert>
// NOLINTNEXTLINE(*)
#define INVARIANT2(CONDITION, REASON) assert((CONDITION) && ((REASON), true))
#define INVARIANT3(CONDITION, REASON, DIAGNOSTICS)                             \
  assert((CONDITION) && ((REASON), true)) /* NOLINT */
// NOLINTNEXTLINE(*)
#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...) assert((CONDITION))
#else

void print_backtrace(std::ostream &out);

std::string get_backtrace();

void report_exception_to_stderr(const invariant_failedt &);

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
#ifdef __GNUC__
__attribute__((noreturn))
#endif
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

/// Takes a backtrace, constructs an invariant_violatedt from reason and the
/// backtrace, aborts printing the invariant's description.
/// In future this may throw rather than aborting.
/// \param file : C string giving the name of the file.
/// \param function : C string giving the name of the function.
/// \param line : The line number of the invariant
/// \param reason : brief description of the invariant violation.
/// \param condition : the condition this invariant is checking.
#ifdef __GNUC__
__attribute__((noreturn))
#endif
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

// These require a trailing semicolon by the user, such that INVARIANT
// behaves syntactically like a function call.
// NOLINT as macro definitions confuse the linter it seems.
#ifdef _MSC_VER
#define __this_function__ __FUNCTION__
#else
#define __this_function__ __func__
#endif

// We wrap macros that take __VA_ARGS__ as an argument with EXPAND_MACRO(). This
// is to account for the behaviour of msvc, which otherwise would not expand
// __VA_ARGS__ to multiple arguments in the outermost macro invocation.
#define EXPAND_MACRO(x) x

#define GET_MACRO(X1, X2, X3, X4, X5, X6, MACRO, ...) MACRO

// This macro dispatches to the macros MACRO<n> (with 1 <= n <= 6) and calls
// them with the arguments in __VA_ARGS__. The invocation of GET_MACRO() selects
// MACRO<n> when __VA_ARGS__ consists of n arguments.
#define REDIRECT(MACRO, ...)                                                   \
  do                                                                           \
  {                                                                            \
    EXPAND_MACRO(                                                              \
      GET_MACRO(                                                               \
        __VA_ARGS__,                                                           \
        MACRO##6,                                                              \
        MACRO##5,                                                              \
        MACRO##4,                                                              \
        MACRO##3,                                                              \
        MACRO##2,                                                              \
        MACRO##1,                                                              \
        DUMMY_MACRO_ARG)(__VA_ARGS__));                                        \
  } while(false)

#define INVARIANT2(CONDITION, REASON)                                          \
  do /* NOLINT */                                                              \
  {                                                                            \
    if(!(CONDITION))                                                           \
      invariant_violated_string(                                               \
        __FILE__,                                                              \
        __this_function__,                                                     \
        __LINE__,                                                              \
        #CONDITION,                                                            \
        (REASON)); /* NOLINT */                                                \
  } while(false)

#define INVARIANT3(CONDITION, REASON, DIAGNOSTICS)                             \
  do /* NOLINT */                                                              \
  {                                                                            \
    if(!(CONDITION))                                                           \
      invariant_violated_structured<invariant_with_diagnostics_failedt>(       \
        __FILE__,                                                              \
        __this_function__,                                                     \
        __LINE__,                                                              \
        #CONDITION,                                                            \
        (REASON),                                                              \
        (DIAGNOSTICS)); /* NOLINT */                                           \
  } while(false)

#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...)                         \
  do /* NOLINT */                                                              \
  {                                                                            \
    if(!(CONDITION))                                                           \
      invariant_violated_structured<TYPENAME>(                                 \
        __FILE__,                                                              \
        __this_function__,                                                     \
        __LINE__,                                                              \
        #CONDITION,                                                            \
        __VA_ARGS__); /* NOLINT */                                             \
  } while(false)

#endif // End CPROVER_DO_NOT_CHECK / CPROVER_ASSERT / ... if block

// Short hand macros. The variants *_STRUCTURED below allow to specify a custom
// exception, and are equivalent to INVARIANT_STRUCTURED.

#define INVARIANT(...) EXPAND_MACRO(REDIRECT(INVARIANT, __VA_ARGS__))

// The condition should only contain (unmodified) inputs to the method. Inputs
// include arguments passed to the function, as well as member variables that
// the function may read.
// "The design of the system means that the arguments to this method
//  will always meet this condition".
//
// The PRECONDITION documents / checks assumptions about the inputs
// that is the caller's responsibility to make happen before the call.
#define PRECONDITION1(CONDITION) INVARIANT2(CONDITION, "Precondition")
#define PRECONDITION2(CONDITION, DIAGNOSTICS)                                  \
  INVARIANT3(CONDITION, "Precondition", DIAGNOSTICS)

#define PRECONDITION(...) EXPAND_MACRO(REDIRECT(PRECONDITION, __VA_ARGS__))

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
#define POSTCONDITION1(CONDITION) INVARIANT2(CONDITION, "Postcondition")
#define POSTCONDITION2(CONDITION, DIAGNOSTICS)                                 \
  INVARIANT3(CONDITION, "Postcondition", DIAGNOSTICS)

#define POSTCONDITION(...) EXPAND_MACRO(REDIRECT(POSTCONDITION, __VA_ARGS__))

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
#define CHECK_RETURN1(CONDITION) INVARIANT2(CONDITION, "Check return value")
#define CHECK_RETURN2(CONDITION, DIAGNOSTICS)                                  \
  INVARIANT3(CONDITION, "Check return value", DIAGNOSTICS)

#define CHECK_RETURN(...) EXPAND_MACRO(REDIRECT(CHECK_RETURN, __VA_ARGS__))

#define CHECK_RETURN_STRUCTURED(CONDITION, TYPENAME, ...)                      \
  EXPAND_MACRO(INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__))

// This should be used to mark dead code
#define UNREACHABLE INVARIANT2(false, "Unreachable")
#define UNREACHABLE_STRUCTURED(TYPENAME, ...)                                  \
  EXPAND_MACRO(INVARIANT_STRUCTURED(false, TYPENAME, __VA_ARGS__))

// This condition should be used to document that assumptions that are
// made on goto_functions, goto_programs, exprts, etc. being well formed.
// "The data structure is not corrupt or malformed"
#define DATA_INVARIANT2(CONDITION, REASON) INVARIANT2(CONDITION, REASON)
#define DATA_INVARIANT3(CONDITION, REASON, DIAGNOSTICS)                        \
  INVARIANT3(CONDITION, REASON, DIAGNOSTICS)

#define DATA_INVARIANT(...) EXPAND_MACRO(REDIRECT(DATA_INVARIANT, __VA_ARGS__))

#define DATA_INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...)                    \
  EXPAND_MACRO(INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__))

// Legacy annotations

// The following should not be used in new code and are only intended
// to migrate documentation and "error handling" in older code.
#define TODO INVARIANT2(false, "Todo")
#define UNIMPLEMENTED INVARIANT2(false, "Unimplemented")
#define UNHANDLED_CASE INVARIANT2(false, "Unhandled case")

#endif // CPROVER_UTIL_INVARIANT_H
