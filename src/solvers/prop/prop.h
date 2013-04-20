/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_H
#define CPROVER_PROP_H

// decision procedure wrapper for boolean propositional logics

#include <util/message.h>

#include "prop_assignment.h"

class tvt;

/*! \brief TO_BE_DOCUMENTED
*/
class propt:public messaget, public prop_assignmentt
{
public:
  propt() { }
  virtual ~propt() { }
 
  // boolean operators
  virtual literalt land(literalt a, literalt b)=0;
  virtual literalt lor(literalt a, literalt b)=0;
  virtual literalt land(const bvt &bv)=0;
  virtual literalt lor(const bvt &bv)=0;
  virtual literalt lnot(literalt a)=0;
  virtual literalt lxor(literalt a, literalt b)=0;
  virtual literalt lxor(const bvt &bv)=0;
  virtual literalt lnand(literalt a, literalt b)=0;
  virtual literalt lnor(literalt a, literalt b)=0;
  virtual literalt lequal(literalt a, literalt b)=0;
  virtual literalt limplies(literalt a, literalt b)=0;
  virtual literalt lselect(literalt a, literalt b, literalt c)=0; // a?b:c
  virtual void set_equal(literalt a, literalt b);

  virtual void l_set_to(literalt a, bool value)
  {
    set_equal(a, const_literal(value));
  }
  
  void l_set_to_true(literalt a)
  { l_set_to(a, true); }
  void l_set_to_false(literalt a)
  { l_set_to(a, false); }

  // constraints
  virtual void lcnf(const bvt &bv)=0;
  virtual bool has_set_to() const { return true; }
  
  // assumptions
  virtual void set_assumptions(const bvt &_assumptions) { }
  virtual bool has_set_assumptions() const { return false; }

  // variables
  virtual literalt new_variable()=0;
  virtual void set_variable_name(literalt a, const std::string &name) { }
  virtual unsigned no_variables() const=0;
  bvt new_variables(unsigned width);
  
  // solving
  virtual const std::string solver_text()=0;
  typedef enum { P_SATISFIABLE, P_UNSATISFIABLE, P_ERROR } resultt;
  virtual resultt prop_solve()=0;  
  
  // satisfying assignment, from prop_assignmentt
  virtual tvt l_get(literalt a) const=0;
  virtual void set_assignment(literalt a, bool value);
  virtual void copy_assignment_from(const propt &prop);

  // returns true if an assumption is in the final conflict
  virtual bool is_in_conflict(literalt l) const;  
  virtual bool has_is_in_conflict() const { return false; }

  // cores -- will be removed
  virtual bool is_in_core(literalt l) const;
  virtual bool has_in_core() const { return false; }
};

#endif
