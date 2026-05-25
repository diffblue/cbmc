/*******************************************************************\

Module: C++ SFINAE context per [temp.deduct]/8

Author: Kiro

\*******************************************************************/

/// \file
/// RAII guard for SFINAE immediate contexts per [temp.deduct]/8 and
/// related rules ([temp.constr.atomic], [temp.alias],
/// [temp.deduct.call], [temp.deduct.conv]).

#ifndef CPROVER_CPP_CPP_SFINAE_CONTEXT_H
#define CPROVER_CPP_CPP_SFINAE_CONTEXT_H

#include <util/message.h>

#include <cstddef>

class cpp_typecheckt;

/// RAII guard marking a SFINAE *immediate context* per
/// [temp.deduct]/8 of N5008 (C++26 working draft):
///
///   > If a substitution results in an invalid type or expression,
///   > type deduction fails.  An invalid type or expression is one
///   > that would be ill-formed, with a diagnostic required, if
///   > written in the same context using the substituted arguments.
///   > …
///   > Invalid types and expressions can result in a deduction
///   > failure only in the *immediate context* of the deduction
///   > substitution loci.
///
/// A conforming implementation therefore needs a way to mark "I am
/// about to perform substitution; a failure here is a deduction
/// failure, not a compilation error".  This class provides that
/// marking as a stack-allocated RAII guard.
///
/// The same semantics apply verbatim to:
///
///  * [temp.constr.atomic]/3: an unsatisfied atomic constraint is a
///    soft failure, not an ill-formed program.
///
///  * [temp.alias]/2: substitution into the defining-type-id of an
///    alias template that fails is a deduction failure.
///
///  * [temp.deduct.call] and [temp.deduct.conv]: per-candidate
///    substitution during overload resolution is SFINAE-guarded.
///
/// Construction semantics:
///  * swaps the typechecker's `message_handlert` to a
///    `null_message_handlert` so errors emitted during substitution
///    are suppressed;
///  * captures the outer error count at entry.
///
/// Destruction semantics:
///  * restores the previous handler; and
///  * resets the error count to the pre-guard value.
///
/// Both happen even when leaving via exception, so the usual SFINAE
/// pattern of a `try`/`catch` to convert a `throw 0` into a
/// deduction-failure signal remains valid (the guard's destructor
/// runs before the outer catch handler executes, so when control
/// reaches the outer handler the typechecker is already back in its
/// pre-guard state).
///
/// Typical usage, modelled on [temp.deduct.call]/1 per-candidate
/// substitution during overload resolution:
///
/// \code
///   sfinae_contextt guard{cpp_typecheck};
///   exprt e;
///   try
///   {
///     e = guess_function_template_args(candidate, fargs);
///   }
///   catch(...)
///   {
///     continue;  // [temp.deduct]/3: a substitution failure causes
///                // the candidate to be silently discarded.  The
///                // `guard` destructor restores handler + error
///                // count before we iterate.
///   }
/// \endcode
///
/// Non-SFINAE contexts (e.g. direct typechecking of user code that
/// genuinely *requires* a diagnostic) must not be wrapped in this
/// guard; doing so would hide real compilation errors.
class sfinae_contextt
{
public:
  explicit sfinae_contextt(cpp_typecheckt &_typecheck);
  ~sfinae_contextt();

  sfinae_contextt(const sfinae_contextt &) = delete;
  sfinae_contextt &operator=(const sfinae_contextt &) = delete;
  sfinae_contextt(sfinae_contextt &&) = delete;
  sfinae_contextt &operator=(sfinae_contextt &&) = delete;

private:
  cpp_typecheckt &typecheck;
  message_handlert *saved_handler;
  std::size_t saved_error_count;
  null_message_handlert null_handler;
};

#endif // CPROVER_CPP_CPP_SFINAE_CONTEXT_H
