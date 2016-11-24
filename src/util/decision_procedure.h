/*******************************************************************\

Module: Decision Procedure Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_DECISION_PROCEDURE_H
#define CPROVER_DECISION_PROCEDURE_H

#include "message.h"

class exprt;
class namespacet;

class decision_proceduret:public messaget
{
public:
  explicit decision_proceduret(const namespacet &_ns):ns(_ns)
  {
  }

  // get a value from satisfying instance if satisfiable
  // returns nil if not available
  virtual exprt get(const exprt &expr) const=0;

  // print satisfying assignment  
  virtual void print_assignment(std::ostream &out) const=0;

  // add constraints
  // the expression must be of Boolean type  
  virtual void set_to(const exprt &expr, bool value)=0;
  
  inline void set_to_true(const exprt &expr)
  { set_to(expr, true); }
   
  inline void set_to_false(const exprt &expr)
  { set_to(expr, false); }
  
  // solve the problem
  typedef enum { D_SATISFIABLE, D_UNSATISFIABLE, D_ERROR } resultt;

  // will eventually be protected, use below call operator  
  virtual resultt dec_solve()=0;
  
  inline resultt operator()()
  {
    return dec_solve();
  }

  // old-style, will go away  
  virtual bool in_core(const exprt &expr);
  
  // return a textual description of the decision procedure
  virtual std::string decision_procedure_text() const=0;
  
protected:
  const namespacet &ns;
};

static inline decision_proceduret & operator << (
  decision_proceduret &dest,
  const exprt &src)
{
  dest.set_to_true(src);
  return dest;
}

#endif
