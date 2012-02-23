/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EXPR_H
#define CPROVER_EXPR_H

#include <type.h>

#define forall_operands(it, expr) \
  if((expr).has_operands()) \
    for(exprt::operandst::const_iterator it=(expr).operands().begin(); \
        it!=(expr).operands().end(); it++)

#define Forall_operands(it, expr) \
  if((expr).has_operands()) \
    for(exprt::operandst::iterator it=(expr).operands().begin(); \
        it!=(expr).operands().end(); it++)

#define forall_expr(it, expr) \
  for(exprt::operandst::const_iterator it=(expr).begin(); \
      it!=(expr).end(); it++)

#define Forall_expr(it, expr) \
  for(exprt::operandst::iterator it=(expr).begin(); \
      it!=(expr).end(); it++)
      
#define forall_expr_list(it, expr) \
  for(expr_listt::const_iterator it=(expr).begin(); \
      it!=(expr).end(); it++)

#define Forall_expr_list(it, expr) \
  for(expr_listt::iterator it=(expr).begin(); \
      it!=(expr).end(); it++)

/*! \brief Base class for all expressions
*/
class exprt:public irept
{
public:
  #ifdef USE_LIST
  typedef std::list<exprt> operandst;
  #else
  typedef std::vector<exprt> operandst;
  #endif

  // constructors
  inline exprt() { }
  inline explicit exprt(const irep_idt &_id):irept(_id) { }
  inline exprt(const irep_idt &_id, const typet &_type):irept(_id) { type()=_type; }
 
  /// returns the type of the expression
  inline typet &type() { return static_cast<typet &>(add(ID_type)); }
  inline const typet &type() const { return static_cast<const typet &>(find(ID_type)); }

  inline bool has_operands() const
  { return !find(ID_operands).is_nil(); }

  inline operandst &operands()
  { return (operandst &)(add(ID_operands).get_sub()); }
  
  inline const operandst &operands() const
  { return (const operandst &)(find(ID_operands).get_sub()); }
   
  inline exprt &op0()
  { return operands().front(); }

  inline exprt &op1()
  #ifdef USE_LIST
  { return *(++operands().begin()); }
  #else
  { return operands()[1]; }
  #endif
   
  inline exprt &op2()
  #ifdef USE_LIST
  { return *(++ ++operands().begin()); }
  #else
  { return operands()[2]; }
  #endif
   
  inline exprt &op3()
  #ifdef USE_LIST
  { return *(++ ++ ++operands().begin()); }
  #else
  { return operands()[3]; }
  #endif
   
  inline const exprt &op0() const
  { return operands().front(); }

  inline const exprt &op1() const
  #ifdef USE_LIST
  { return *(++operands().begin()); }
  #else
  { return operands()[1]; }
  #endif
  
  inline const exprt &op2() const
  #ifdef USE_LIST
  { return *(++ ++operands().begin()); }
  #else
  { return operands()[2]; }
  #endif
  
  inline const exprt &op3() const
  #ifdef USE_LIST
  { return *(++ ++ ++operands().begin()); }
  #else
  { return operands()[3]; }
  #endif
  
  inline void reserve_operands(unsigned n)
  #ifdef USE_LIST
  { }
  #else
  { operands().reserve(n) ; }
  #endif
   
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
  
  const locationt &find_location() const;

  inline const locationt &location() const
  {
    return static_cast<const locationt &>(find(ID_C_location));
  }

  inline locationt &location()
  {
    return static_cast<locationt &>(add(ID_C_location));
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
