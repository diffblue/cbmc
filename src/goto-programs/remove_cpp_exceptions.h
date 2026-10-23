/*******************************************************************\

Module: Remove C++ exceptions (goto-level lowering)

Author: Kiro

\*******************************************************************/

/// \file
/// Lower C++ exceptions (CATCH-PUSH/CATCH-POP/THROW) to ordinary control flow
/// (GOTOs and assignments) before symbolic execution, so that goto-symex does
/// not need to model exceptions.  A thrown value is delivered to the matching
/// handler's parameter and the handler body becomes reachable.
///
/// This is the C++ counterpart of JBMC's remove_exceptions: C++ exceptions are
/// value types matched by cpp_exception_id type tags (which already include
/// base classes), rather than Java reference types matched by instanceof.

#ifndef CPROVER_GOTO_PROGRAMS_REMOVE_CPP_EXCEPTIONS_H
#define CPROVER_GOTO_PROGRAMS_REMOVE_CPP_EXCEPTIONS_H

class goto_modelt;
class message_handlert;

/// Lowers C++ CATCH-PUSH/CATCH-POP/THROW instructions to gotos/assignments.
/// A no-op for goto programs that contain no such instructions.
void remove_cpp_exceptions(goto_modelt &, message_handlert &);

#endif // CPROVER_GOTO_PROGRAMS_REMOVE_CPP_EXCEPTIONS_H
