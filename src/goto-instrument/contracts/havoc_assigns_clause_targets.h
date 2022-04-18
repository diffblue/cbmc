/*******************************************************************\

Module: Havoc multiple and possibly dependent targets simultaneously

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/

/// \file
/// Havoc function assigns clauses

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_HAVOC_ASSIGNS_CLAUSE_TARGETS_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_HAVOC_ASSIGNS_CLAUSE_TARGETS_H

#include "instrument_spec_assigns.h"
#include <util/expr.h>

class namespacet;
class symbol_tablet;
class goto_programt;
class goto_functionst;
class message_handlert;

/// Class to generate havocking instructions for target expressions of a
/// function contract's assign clause (replacement).
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
class havoc_assigns_clause_targetst : public instrument_spec_assignst
{
public:
  /// \param _function_id Name of the replaced function
  /// \param _targets Assigns clause targets of the replaced function
  /// \param _functions Other functions forming the GOTO model
  /// \param _source_location Source location of the replaced function call
  ///        (added to all generated instructions)
  /// \param _st Symbol table of the model (new symbols will be added)
  /// \param _message_handler handler used to log translation warnings/errors
  ///
  havoc_assigns_clause_targetst(
    const irep_idt &_function_id,
    const std::vector<exprt> &_targets,
    const goto_functionst &_functions,
    const source_locationt &_source_location,
    symbol_tablet &_st,
    message_handlert &_message_handler)
    : instrument_spec_assignst(_function_id, _functions, _st, _message_handler),
      targets(_targets),
      source_location(_source_location)
  {
  }

  /// Generates the assigns clause replacement instructions in dest.
  void get_instructions(goto_programt &dest);

private:
  /// \brief Generates instructions to conditionally havoc the given conditional
  /// address range expression `car`, adding results to `dest`.
  ///
  /// Adds a special comment on the havoc instructions in order to trace back
  /// the origin of the havoc expressions to the function being replaced.
  ///
  /// Generates these instructions for a `__CPROVER_POINTER_OBJECT(...)` target:
  ///
  /// ```
  /// IF !__car_writable GOTO skip_target
  /// OTHER havoc_object(_car_lb)
  /// skip_target: SKIP
  /// DEAD __car_writable
  /// DEAD __car_lb
  /// DEAD __car_ub
  /// ```
  ///
  /// Generates these instructions for an object slice target:
  /// ```
  /// IF !__car_writable GOTO skip_target
  /// __CPROVER_havoc_slize(__car_lb, car.target_size)
  /// skip_target: SKIP
  /// DEAD __car_writable
  /// DEAD __car_lb
  /// DEAD __car_ub
  /// ```
  ///
  /// And generate these instructions otherwise:
  ///
  /// ```
  /// IF !__car_writable GOTO skip_target
  /// ASSIGN *((target_type *) _car_lb) = nondet(target_type);
  /// skip_target: SKIP
  /// DEAD __car_writable
  /// DEAD __car_lb
  /// DEAD __car_ub
  /// ```
  /// Where `target_type` is the type of the target expression.
  void havoc_if_valid(car_exprt car, goto_programt &dest);

  /// Havoc a static local expression
  void havoc_static_local(car_exprt car, goto_programt &dest);

  const std::vector<exprt> &targets;
  const source_locationt &source_location;
};
#endif // CPROVER_GOTO_INSTRUMENT_CONTRACTS_HAVOC_ASSIGNS_CLAUSE_TARGETS_H
