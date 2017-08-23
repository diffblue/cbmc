/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_INVARIANT_H
#define CPROVER_UTIL_INVARIANT_H

#include <stdexcept>
#include <type_traits>
#include <string>
#include <cstdlib>

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
class invariant_failedt: public std::logic_error
{
 private:
  std::string get_invariant_failed_message(
    const std::string &file,
    const std::string &function,
    int line,
    const std::string &backtrace,
    const std::string &reason);

 public:

  const std::string file;
  const std::string function;
  const int line;
  const std::string backtrace;
  const std::string reason;

  invariant_failedt(
    const std::string &_file,
    const std::string &_function,
    int _line,
    const std::string &_backtrace,
    const std::string &_reason):
    logic_error(
      get_invariant_failed_message(
        _file,
        _function,
        _line,
        _backtrace,
        _reason)),
    file(_file),
    function(_function),
    line(_line),
    backtrace(_backtrace),
    reason(_reason)
  {
  }
};

#if defined(CPROVER_INVARIANT_CPROVER_ASSERT)
// Used to allow CPROVER to check itself
#define INVARIANT(CONDITION, REASON) \
  __CPROVER_assert((CONDITION), "Invariant : " REASON)


#elif defined(CPROVER_INVARIANT_DO_NOT_CHECK)
// For performance builds, invariants can be ignored
// This is *not* recommended as it can result in unpredictable behaviour
// including silently reporting incorrect results.
// This is also useful for checking side-effect freedom.
#define INVARIANT(CONDITION, REASON, ...) do {} while(0)

#elif defined(CPROVER_INVARIANT_ASSERT)
// Not recommended but provided for backwards compatability
#include <cassert>
// NOLINTNEXTLINE(*)
#define INVARIANT(CONDITION, REASON, ...) assert((CONDITION) && ((REASON), true))

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
/// \param params : (variadic) parameters to forward to ET's constructor
///  its backtrace member will be set before it is used.
template<class ET, typename ...Params>
#ifdef __GNUC__
__attribute__((noreturn))
#endif
typename std::enable_if<std::is_base_of<invariant_failedt, ET>::value>::type
invariant_violated_structured(
  const std::string &file,
  const std::string &function,
  const int line,
  Params &&... params)
{
  std::string backtrace=get_backtrace();
  ET to_throw(file, function, line, backtrace, std::forward<Params>(params)...);
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
#ifdef __GNUC__
__attribute__((noreturn))
#endif
inline void invariant_violated_string(
  const std::string &file,
  const std::string &function,
  const int line,
  const std::string &reason)
{
  invariant_violated_structured<invariant_failedt>(
    file,
    function,
    line,
    reason);
}

// These require a trailing semicolon by the user, such that INVARIANT
// behaves syntactically like a function call.
// NOLINT as macro definitions confuse the linter it seems.
#ifdef _MSC_VER
#define __this_function__ __FUNCTION__
#else
#define __this_function__ __func__
#endif

#define INVARIANT(CONDITION, REASON) \
  do /* NOLINT */ \
  { \
  if(!(CONDITION)) \
    invariant_violated_string(__FILE__, __this_function__, __LINE__, (REASON)); /* NOLINT */  \
  } while(0)

#define INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...) \
  do /* NOLINT */ \
  { \
  if(!(CONDITION)) \
    invariant_violated_structured<TYPENAME>(__FILE__, __this_function__, __LINE__, __VA_ARGS__); /* NOLINT */ \
  } while(0)

#endif // End CPROVER_DO_NOT_CHECK / CPROVER_ASSERT / ... if block

// Short hand macros. The second variant of each one permits including an
// explanation or structured exception, in which case they are synonyms
// for INVARIANT.

// The condition should only contain (unmodified) arguments to the method.
// "The design of the system means that the arguments to this method
//  will always meet this condition".
#define PRECONDITION(CONDITION) INVARIANT(CONDITION, "Precondition")
#define PRECONDITION_STRUCTURED(CONDITION, TYPENAME, ...) \
  INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__)

// The condition should only contain variables that will be returned /
// output without further modification.
// "The implementation of this method means that the condition will hold".
#define POSTCONDITION(CONDITION) INVARIANT(CONDITION, "Postcondition")
#define POSTCONDITION_STRUCTURED(CONDITION, TYPENAME, ...) \
  INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__)

// The condition should only contain (unmodified) values that were
// changed by a previous method call.
// "The contract of the previous method call means the following
//  condition holds".
#define CHECK_RETURN(CONDITION) INVARIANT(CONDITION, "Check return value")
#define CHECK_RETURN_STRUCTURED(CONDITION, TYPENAME, ...)  \
  INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__)

// This should be used to mark dead code
#define UNREACHABLE INVARIANT(false, "Unreachable")
#define UNREACHABLE_STRUCTURED(TYPENAME, ...) \
  INVARIANT_STRUCTURED(false, TYPENAME, __VA_ARGS__)

// This condition should be used to document that assumptions that are
// made on goto_functions, goto_programs, exprts, etc. being well formed.
// "The data structure is corrupt or malformed"
#define DATA_INVARIANT(CONDITION, REASON) INVARIANT(CONDITION, REASON)
#define DATA_INVARIANT_STRUCTURED(CONDITION, TYPENAME, ...) \
  INVARIANT_STRUCTURED(CONDITION, TYPENAME, __VA_ARGS__)

// Legacy annotations

// The following should not be used in new code and are only intended
// to migrate documentation and "error handling" in older code
#define TODO           INVARIANT(0, "Todo")
#define UNIMPLEMENTED  INVARIANT(0, "Unimplemented")
#define UNHANDLED_CASE INVARIANT(0, "Unhandled case")

#endif // CPROVER_UTIL_INVARIANT_H
