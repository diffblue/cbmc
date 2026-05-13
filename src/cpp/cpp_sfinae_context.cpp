/*******************************************************************\

Module: C++ SFINAE context per [temp.deduct]/8

Author: Kiro

\*******************************************************************/

/// \file
/// RAII guard for SFINAE immediate contexts per [temp.deduct]/8 of
/// N5008.  See `cpp_sfinae_context.h` for the class-level
/// specification.

#include "cpp_sfinae_context.h"

#include "cpp_typecheck.h"

sfinae_contextt::sfinae_contextt(cpp_typecheckt &_typecheck)
  : typecheck(_typecheck),
    saved_handler(&_typecheck.get_message_handler()),
    saved_error_count(
      _typecheck.get_message_handler().get_message_count(messaget::M_ERROR))
{
  // [temp.deduct]/8: a substitution failure inside the immediate
  // context must not produce a user-visible diagnostic; redirect to
  // a null handler for the duration of the guard.
  typecheck.set_message_handler(null_handler);
}

sfinae_contextt::~sfinae_contextt()
{
  // Restore handler first, so that setting the message count goes
  // to the real handler rather than the null one.
  typecheck.set_message_handler(*saved_handler);
  // Roll the error count back to the pre-guard value.  Any errors
  // emitted inside the guarded region were either absorbed by the
  // null handler (visible nowhere) or counted against the real
  // handler (if code retrieved it via `get_message_handler()`
  // directly); either way, they are not meaningful outside the
  // SFINAE context.
  typecheck.get_message_handler().set_message_count(
    messaget::M_ERROR, saved_error_count);
}
