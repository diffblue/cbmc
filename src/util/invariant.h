/*******************************************************************\

Module:

Author: Martin Brain, martin.brain@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_INVARIANT_H
#define CPROVER_UTIL_INVARIANT_H

#include <stdexcept>

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

class invariant_failedt: public std::logic_error
{
public:
  explicit invariant_failedt(const std::string& what) : logic_error(what) {}
  explicit invariant_failedt(const char* what) : logic_error(what) {}
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
#define INVARIANT(CONDITION, REASON) do {} while(0)


#elif defined(CPROVER_INVARIANT_ASSERT)
// Not recommended but provided for backwards compatability
#include <cassert>
// NOLINTNEXTLINE(*)
#define INVARIANT(CONDITION, REASON) assert((CONDITION) && (REASON))


#else
// CPROVER_INVARIANT_PRINT_STACK_TRACE affects the implementation of
// this function but not it's generation from the macro

void check_invariant(
  const char * const file,
  const char * const function,
  const int line,
  const bool condition,
  const char * const reason);

#ifdef _MSC_VER
#define INVARIANT(CONDITION, REASON) \
  check_invariant(__FILE__, __FUNCTION__, __LINE__, (CONDITION), (REASON))
#else
#define INVARIANT(CONDITION, REASON)                                    \
  check_invariant(__FILE__, __func__, __LINE__, (CONDITION), (REASON))
#endif


#endif



// Short hand macros

// The condition should only contain (unmodified) arguments to the method.
// "The design of the system means that the arguments to this method
//  will always meet this condition".
#define PRECONDITION(CONDITION) INVARIANT(CONDITION, "Precondition")

// The condition should only contain variables that will be returned /
// output without further modification.
// "The implementation of this method means that the condition will hold".
#define POSTCONDITION(CONDITION) INVARIANT(CONDITION, "Postcondition")

// The condition should only contain (unmodified) values that were
// changed by a previous method call.
// "The contract of the previous method call means the following
//  condition holds".
#define CHECK_RETURN(CONDITION) INVARIANT(CONDITION, "Check return value")

// This should be used to mark dead code
#define UNREACHABLE INVARIANT(false, "Unreachable")

// This condition should be used to document that assumptions that are
// made on goto_functions, goto_programs, exprts, etc. being well formed.
// "The data structure is corrupt or malformed"
#define DATA_INVARIANT(CONDITION, REASON) INVARIANT(CONDITION, REASON)


// Legacy annotations

// The following should not be used in new code and are only intended
// to migrate documentation and "error handling" in older code
#define TODO           INVARIANT(0, "Todo")
#define UNIMPLEMENTED  INVARIANT(0, "Unimplemented")
#define UNHANDLED_CASE INVARIANT(0, "Unhandled case")

#endif // CPROVER_UTIL_INVARIANT_H
