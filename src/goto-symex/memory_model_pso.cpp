/*******************************************************************\

Module: Memory model for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

/// \file
/// Memory model for partial order concurrency

#include "memory_model_pso.h"

void memory_model_psot::operator()(symex_target_equationt &equation)
{
  statistics() << "Adding PSO constraints" << eom;

  build_event_lists(equation);
  build_clock_type();

  read_from(equation);
  write_serialization_external(equation);
  program_order(equation);
#ifndef CPROVER_MEMORY_MODEL_SUP_CLOCK
  from_read(equation);
#endif
}

bool memory_model_psot::program_order_is_relaxed(
  partial_order_concurrencyt::event_it e1,
  partial_order_concurrencyt::event_it e2) const
{
  PRECONDITION(e1->is_shared_read() || e1->is_shared_write());
  PRECONDITION(e2->is_shared_read() || e2->is_shared_write());

  // no po relaxation within atomic sections
  if(e1->atomic_section_id!=0 &&
     e1->atomic_section_id==e2->atomic_section_id)
    return false;

  // no relaxation if induced wsi
  if(e1->is_shared_write() && e2->is_shared_write() &&
     address(e1)==address(e2))
    return false;

  // only read/read and read/write are maintained
  return e1->is_shared_write();
}
