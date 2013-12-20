/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_PROP_CONV_STORE_H
#define CPROVER_PROP_CONV_STORE_H

#include "prop_conv.h"

class prop_conv_storet:public prop_convt
{
public:
  prop_conv_storet(const namespacet &_ns):prop_convt(_ns)
  {
  }
  
  struct constraintt
  {
    typedef enum { NONE, CONVERT, SET_TO } typet;
    typet type;
    
    exprt expr;
    
    // for set_to
    bool value;
    
    // for convert
    literalt literal;
    
    void replay(prop_convt &dest) const;
    void print(std::ostream &out) const;
  };

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

  // overloading
  virtual void set_to(const exprt &expr, bool value);
  virtual literalt convert(const exprt &expr);
  
protected:
  constraintst constraints;
};

#endif
