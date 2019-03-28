/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_PROP_PROP_CONV_H
#define CPROVER_SOLVERS_PROP_PROP_CONV_H

#include <string>
#include <map>

#include <util/expr.h>
#include <util/message.h>
#include <util/std_expr.h>

#include "decision_procedure.h"
#include "literal.h"
#include "literal_expr.h"
#include "prop.h"

// API that provides a "handle" in the form of a literalt
// for expressions.

class prop_convt:public decision_proceduret
{
public:
  virtual ~prop_convt() { }

  using decision_proceduret::operator();

  // incremental solving
  virtual void set_frozen(literalt a);
  virtual void set_frozen(const bvt &);
  virtual void set_assumptions(const bvt &_assumptions);
  virtual bool has_set_assumptions() const { return false; }
  virtual void set_all_frozen() {}

  // returns true if an assumption is in the final conflict
  virtual bool is_in_conflict(literalt l) const;
  virtual bool has_is_in_conflict() const { return false; }
};

//
// an instance of the above that converts the
// propositional skeleton by passing it to a propt
//

#endif // CPROVER_SOLVERS_PROP_PROP_CONV_H
