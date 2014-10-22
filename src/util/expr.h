/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EXPR_H
#define CPROVER_EXPR_H

#define OPERANDS_IN_GETSUB

#include "type.h"

#define forall_operands(it, expr) \
  if((expr).has_operands()) \
    for(exprt::operandst::const_iterator it=(expr).operands().begin(), \
        it##_end=(expr).operands().end(); \
        it!=it##_end; ++it)

#define Forall_operands(it, expr) \
  if((expr).has_operands()) \
    for(exprt::operandst::iterator it=(expr).operands().begin(); \
        it!=(expr).operands().end(); ++it)

#define forall_expr(it, expr) \
  for(exprt::operandst::const_iterator it=(expr).begin(); \
      it!=(expr).end(); ++it)

#define Forall_expr(it, expr) \
  for(exprt::operandst::iterator it=(expr).begin(); \
      it!=(expr).end(); ++it)
      
#define forall_expr_list(it, expr) \
  for(expr_listt::const_iterator it=(expr).begin(); \
      it!=(expr).end(); ++it)

#define Forall_expr_list(it, expr) \
  for(expr_listt::iterator it=(expr).begin(); \
      it!=(expr).end(); ++it)

/*! \brief Base class for all expressions
*/
class exprt:public irept
{
public:
  typedef std::vector<exprt> operandst;

  // constructors
  inline exprt() { }
  inline explicit exprt(const irep_idt &_id):irept(_id) { }
  inline exprt(const irep_idt &_id, const typet &_type):irept(_id) { add(ID_type, _type); }
 
  // returns the type of the expression
  inline typet &type() { return static_cast<typet &>(add(ID_type)); }
  inline const typet &type() const { return static_cast<const typet &>(find(ID_type)); }

  // returns true if there is at least one operand
  inline bool has_operands() const
  { return !operands().empty(); }

  inline operandst &operands()
  #ifdef OPERANDS_IN_GETSUB
  { return (operandst &)get_sub(); }
  #else
  { return (operandst &)(add(ID_operands).get_sub()); }
  #endif
  
  inline const operandst &operands() const
  #ifdef OPERANDS_IN_GETSUB
  { return (const operandst &)get_sub(); }
  #else
  { return (const operandst &)(find(ID_operands).get_sub()); }
  #endif
   
  inline exprt &op0()
  { return operands().front(); }

  inline exprt &op1()
  { return operands()[1]; }
   
  inline exprt &op2()
  { return operands()[2]; }
   
  inline exprt &op3()
  { return operands()[3]; }
   
  inline const exprt &op0() const
  { return operands().front(); }

  inline const exprt &op1() const
  { return operands()[1]; }
  
  inline const exprt &op2() const
  { return operands()[2]; }
  
  inline const exprt &op3() const
  { return operands()[3]; }
  
  inline void reserve_operands(operandst::size_type n)
  { operands().reserve(n) ; }
   
  void move_to_operands(exprt &expr); // destroys expr
  void move_to_operands(exprt &e1, exprt &e2); // destroys e1, e2
  void move_to_operands(exprt &e1, exprt &e2, exprt &e3); // destroys e1, e2, e3
  void copy_to_operands(const exprt &expr); // does not destroy expr
  void copy_to_operands(const exprt &e1, const exprt &e2); // does not destroy expr
  void copy_to_operands(const exprt &e1, const exprt &e2, const exprt &e3); // does not destroy expr

  // the following are deprecated -- use constructors instead
  void make_typecast(const typet &_type);
  void make_not();

  void make_true();
  void make_false();
  void make_bool(bool value);
  void negate();

  bool sum(const exprt &expr);
  bool mul(const exprt &expr);
  bool subtract(const exprt &expr);
  
  bool is_constant() const;
  bool is_true() const;
  bool is_false() const;
  bool is_zero() const;
  bool is_one() const;
  bool is_boolean() const;
  
  friend bool operator<(const exprt &X, const exprt &Y);
  
  // will go away
  inline const source_locationt &find_location() const { return find_source_location(); }

  const source_locationt &find_source_location() const;

  // will go away
  inline const source_locationt &location() const
  {
    return static_cast<const source_locationt &>(find(ID_C_source_location));
  }

  inline const source_locationt &source_location() const
  {
    return static_cast<const source_locationt &>(find(ID_C_source_location));
  }

  inline source_locationt &add_source_location()
  {
    return static_cast<source_locationt &>(add(ID_C_source_location));
  }
  
  inline exprt &add_expr(const irep_idt &name)
  {
    return static_cast<exprt &>(add(name));
  }

  inline const exprt &find_expr(const irep_idt &name) const
  {
    return static_cast<const exprt &>(find(name));
  }
  
  void visit(class expr_visitort &visitor);
  void visit(class const_expr_visitort &visitor) const;
};

typedef std::list<exprt> expr_listt;

class expr_visitort
{
public:
  virtual ~expr_visitort() { }
  virtual void operator()(exprt &expr) { }
};

class const_expr_visitort
{
public:
  virtual ~const_expr_visitort() { }
  virtual void operator()(const exprt &expr) { }
};

#endif
