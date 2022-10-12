/*******************************************************************\

Module: Flatten OK Expressions

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_CPROVER_FLATTEN_OK_EXPR_H
#define CPROVER_CPROVER_FLATTEN_OK_EXPR_H

class exprt;
class state_ok_exprt;

// X_ok(p, s) <-->
//   live_object(p)
// ∧ offset(p)+s≤object_size(p)
// ∧ writeable_object(p)           if applicable

exprt flatten(const state_ok_exprt &);

#endif // CPROVER_CPROVER_FLATTEN_OK_EXPR_H
