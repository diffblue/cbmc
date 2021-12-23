/*******************************************************************\

Module: Havoc multiple and possibly dependent targets simultaneously

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Havoc function assigns clauses

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_HAVOC_ASSIGNS_CLAUSE_TARGETS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_HAVOC_ASSIGNS_CLAUSE_TARGETS_H

#include <util/expr.h>

class namespacet;
class symbol_tablet;
class goto_programt;
class message_handlert;

/// Generates havocking instructions for target expressions of a
/// function contract's assign clause (replacement).
///
/// \param replaced_function_id Name of the replaced function
/// \param targets Assigns clause targets
/// \param dest Destination program where the instructions are generated
/// \param source_location Source location of the replaced function call
///        (added to all generated instructions)
/// \param mode Language mode to use for newly generated symbols
/// \param ns Namespace of the model
/// \param st Symbol table of the model (new symbols will be added)
/// \param message_handler handler used to log translation warnings/errors
///
/// Assigns clause targets can be interdependent as shown in this example:
///
/// ```
/// typedef struct vect { int *arr; int size; } vect;
/// void resize(vect *v)
/// __CPROVER_assigns(v->arr, v->size, __CPROVER_POINTER_OBJECT(v->arr))
/// {
///   free(v->arr);
///   v->size += 10 * sizeof(int);
///   v->arr = malloc(v->size);
/// }
/// ```
///
/// To havoc these dependent targets simultaneously, we first take snapshots
/// of their addresses, and havoc them in a second time.
/// Snapshotting and havocking are both guarded by the validity of the target.
///
void havoc_assigns_clause_targets(
  const irep_idt &replaced_function_id,
  const std::vector<exprt> &targets,
  goto_programt &dest,
  // context parameters
  const source_locationt &source_location,
  const irep_idt &mode,
  namespacet &ns,
  symbol_tablet &st,
  message_handlert &message_handler);

bool is_assigns_clause_replacement_tracking_comment(const irep_idt &comment);

#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_HAVOC_ASSIGNS_CLAUSE_TARGETS_H
