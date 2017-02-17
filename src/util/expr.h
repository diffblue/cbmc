/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXPR_H
#define CPROVER_UTIL_EXPR_H

#define OPERANDS_IN_GETSUB

#include "type.h"

#define forall_operands(it, expr) \
  if((expr).has_operands()) /* NOLINT(readability/braces) */ \
    for(exprt::operandst::const_iterator it=(expr).operands().begin(), \
        it##_end=(expr).operands().end(); \
        it!=it##_end; ++it)

#define Forall_operands(it, expr) \
  if((expr).has_operands()) /* NOLINT(readability/braces) */ \
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
  exprt() { }
  explicit exprt(const irep_idt &_id):irept(_id) { }
  exprt(const irep_idt &_id, const typet &_type):irept(_id)
  {
    add(ID_type, _type);
  }

  // returns the type of the expression
  typet &type() { return static_cast<typet &>(add(ID_type)); }
  const typet &type() const
  {
    return static_cast<const typet &>(find(ID_type));
  }

  // returns true if there is at least one operand
  bool has_operands() const
  { return !operands().empty(); }

  operandst &operands()
  #ifdef OPERANDS_IN_GETSUB
  { return (operandst &)get_sub(); }
  #else
  { return (operandst &)(add(ID_operands).get_sub()); }
  #endif

  const operandst &operands() const
  #ifdef OPERANDS_IN_GETSUB
  { return (const operandst &)get_sub(); }
  #else
  { return (const operandst &)(find(ID_operands).get_sub()); }
  #endif

  exprt &op0()
  { return operands().front(); }

  exprt &op1()
  { return operands()[1]; }

  exprt &op2()
  { return operands()[2]; }

  exprt &op3()
  { return operands()[3]; }

  const exprt &op0() const
  { return operands().front(); }

  const exprt &op1() const
  { return operands()[1]; }

  const exprt &op2() const
  { return operands()[2]; }

  const exprt &op3() const
  { return operands()[3]; }

  void reserve_operands(operandst::size_type n)
  { operands().reserve(n) ; }

  // destroys expr, e1, e2, e3
  void move_to_operands(exprt &expr);
  void move_to_operands(exprt &e1, exprt &e2);
  void move_to_operands(exprt &e1, exprt &e2, exprt &e3);
  // does not destroy expr, e1, e2, e3
  void copy_to_operands(const exprt &expr);
  void copy_to_operands(const exprt &e1, const exprt &e2);
  void copy_to_operands(const exprt &e1, const exprt &e2, const exprt &e3);

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

  const source_locationt &find_source_location() const;

  const source_locationt &source_location() const
  {
    return static_cast<const source_locationt &>(find(ID_C_source_location));
  }

  source_locationt &add_source_location()
  {
    return static_cast<source_locationt &>(add(ID_C_source_location));
  }

  exprt &add_expr(const irep_idt &name)
  {
    return static_cast<exprt &>(add(name));
  }

  const exprt &find_expr(const irep_idt &name) const
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

#endif // CPROVER_UTIL_EXPR_H
