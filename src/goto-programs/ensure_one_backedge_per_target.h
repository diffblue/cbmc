/*******************************************************************\

Module: Ensure one backedge per target

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Ensure one backedge per target

#ifndef CPROVER_GOTO_PROGRAMS_ENSURE_ONE_BACKEDGE_PER_TARGET_H
#define CPROVER_GOTO_PROGRAMS_ENSURE_ONE_BACKEDGE_PER_TARGET_H

#include "goto_model.h"
#include "goto_program.h"

/// Try to force the given \p goto_program into a form such that each backedge
/// (branch going backwards in lexical program order) has a unique target. This
/// is achieved by redirecting backedges or possibly introducing a new one.
/// Note this may not always succeed; client code must check whether the
/// condition holds of any backedge target it is interested in.
/// Note this overload leaves \p goto_program's location numbers and incoming-
/// edges sets inconsistent; the client should call \ref goto_programt::update.
/// \return true if any change is made.
bool ensure_one_backedge_per_target(goto_programt &goto_program);

/// Try to force the given \p goto_program into a form such that each backedge
/// (branch going backwards in lexical program order) has a unique target. This
/// is achieved by redirecting backedges or possibly introducing a new one.
/// Note this may not always succeed; client code must check whether the
/// condition holds of any backedge target it is interested in.
/// Note this overload updates \p goto_model_function's location numbers and
/// incoming-edges sets.
/// \return true if any change is made.
bool ensure_one_backedge_per_target(goto_model_functiont &goto_model_function);

/// Try to force the given \p goto_program into a form such that each backedge
/// (branch going backwards in lexical program order) has a unique target. This
/// is achieved by redirecting backedges or possibly introducing a new one.
/// Note this may not always succeed; client code must check whether the
/// condition holds of any backedge target it is interested in.
/// Note this overload updates \p goto_model's location numbers and
/// incoming-edges sets.
/// \return true if any change is made.
bool ensure_one_backedge_per_target(goto_modelt &goto_model);

#endif // CPROVER_GOTO_PROGRAMS_ENSURE_ONE_BACKEDGE_PER_TARGET_H
