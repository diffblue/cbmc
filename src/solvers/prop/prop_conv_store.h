/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_CONV_STORE_H
#define CPROVER_PROP_CONV_STORE_H

#include "../sat/cnf_clause_list.h"
#include "prop_conv.h"

class prop_conv_store_propt
{
public:
  cnf_clause_list_assignmentt prop_store;
};

struct prop_conv_store_constraintt
{
  typedef enum { NONE, CONVERT_REST, SET_TO } typet;
  typet type;
  
  exprt expr;
  
  // for SET_TO
  bool value;
  
  // for CONVERT_REST
  literalt literal;
  
  void replay(prop_convt &dest) const;
  void print(std::ostream &out) const;
};

class prop_conv_storet:
  public prop_conv_store_propt,
  public prop_convt
{
public:
  prop_conv_storet(const namespacet &_ns):prop_convt(_ns, prop_store)
  {
  }
  
  // overloading
  virtual void set_to(const exprt &expr, bool value);
  
  typedef prop_conv_store_constraintt constraintt;

  class constraintst
  {
  public:
    typedef std::list<constraintt> constraint_listt;
    constraint_listt constraint_list;
    
    constraintt &add_constraint()
    {
      constraint_list.push_back(constraintt());
      return constraint_list.back();
    }
    
    void replay(prop_convt &dest) const;
    void print(std::ostream &out) const;
  };
  
  const constraintst &get_constraints() const
  {
    return constraints;
  }
  
protected:
  // overloading
  virtual literalt convert_rest(const exprt &expr);

  constraintst constraints;
};

#endif
