/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXPR_H
#define CPROVER_UTIL_EXPR_H

#include "type.h"

#include <functional>
#include <list>

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

class depth_iteratort;
class const_depth_iteratort;
class const_unique_depth_iteratort;

/// Base class for all expressions.
/// Inherits from \ref irept and has operands (stored as unnamed children of
/// `irept`), and a type (which is a named sub with identifier `ID_type`).
/// The class contains functions to access and modify the operands, as well as
/// visitor utilities.
///
/// The example below shows the irept structure of the sum of integers
/// 3 and 5.
/// \dotfile expr.dot
/// Some context available here: \ref exprt_section
/// "exprt section in util module"
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

  /// Return the type of the expression
  typet &type() { return static_cast<typet &>(add(ID_type)); }
  const typet &type() const
  {
    return static_cast<const typet &>(find(ID_type));
  }

  /// Return true if there is at least one operand.
  bool has_operands() const
  { return !operands().empty(); }

  operandst &operands()
  { return (operandst &)get_sub(); }

  const operandst &operands() const
  { return (const operandst &)get_sub(); }

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

  DEPRECATED("use copy_to_operands(expr) instead")
  void move_to_operands(exprt &expr);

  DEPRECATED("use copy_to_operands(e1, e2) instead")
  void move_to_operands(exprt &e1, exprt &e2);

  DEPRECATED("use copy_to_operands(e1, e2, e3) instead")
  void move_to_operands(exprt &e1, exprt &e2, exprt &e3);

  /// Copy the given argument to the end of `exprt`'s operands.
  /// \param expr: `exprt` to append to the operands
  void copy_to_operands(const exprt &expr)
  {
    operands().push_back(expr);
  }

  /// Copy the given argument to the end of `exprt`'s operands.
  /// \param expr: `exprt` to append to the operands
  void copy_to_operands(exprt &&expr)
  {
    operands().push_back(std::move(expr));
  }

  /// Copy the given arguments to the end of `exprt`'s operands.
  /// \param e1: first `exprt` to append to the operands
  /// \param e2: second `exprt` to append to the operands
  void copy_to_operands(const exprt &e1, const exprt &e2)
  {
    operandst &op = operands();
    #ifndef USE_LIST
    op.reserve(op.size() + 2);
    #endif
    op.push_back(e1);
    op.push_back(e2);
  }

  /// Copy the given arguments to the end of `exprt`'s operands.
  /// \param e1: first `exprt` to append to the operands
  /// \param e2: second `exprt` to append to the operands
  void copy_to_operands(exprt &&e1, exprt &&e2)
  {
    operandst &op = operands();
    #ifndef USE_LIST
    op.reserve(op.size() + 2);
    #endif
    op.push_back(std::move(e1));
    op.push_back(std::move(e2));
  }

  /// Copy the given arguments to the end of `exprt`'s operands.
  /// \param e1: first `exprt` to append to the operands
  /// \param e2: second `exprt` to append to the operands
  /// \param e3: third `exprt` to append to the operands
  void copy_to_operands(const exprt &e1, const exprt &e2, const exprt &e3)
  {
    operandst &op = operands();
    #ifndef USE_LIST
    op.reserve(op.size() + 3);
    #endif
    op.push_back(e1);
    op.push_back(e2);
    op.push_back(e3);
  }

  /// Copy the given arguments to the end of `exprt`'s operands.
  /// \param e1: first `exprt` to append to the operands
  /// \param e2: second `exprt` to append to the operands
  /// \param e3: third `exprt` to append to the operands
  void copy_to_operands(exprt &&e1, exprt &&e2, exprt &&e3)
  {
    operandst &op = operands();
    #ifndef USE_LIST
    op.reserve(op.size() + 3);
    #endif
    op.push_back(std::move(e1));
    op.push_back(std::move(e2));
    op.push_back(std::move(e3));
  }

  void make_typecast(const typet &_type);
  void make_not();

  void make_true();
  void make_false();
  void make_bool(bool value);

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

protected:
  exprt &add_expr(const irep_idt &name)
  {
    return static_cast<exprt &>(add(name));
  }

  const exprt &find_expr(const irep_idt &name) const
  {
    return static_cast<const exprt &>(find(name));
  }

public:
  void visit(class expr_visitort &visitor);
  void visit(class const_expr_visitort &visitor) const;

  depth_iteratort depth_begin();
  depth_iteratort depth_end();
  const_depth_iteratort depth_begin() const;
  const_depth_iteratort depth_end() const;
  const_depth_iteratort depth_cbegin() const;
  const_depth_iteratort depth_cend() const;
  depth_iteratort depth_begin(std::function<exprt &()> mutate_root) const;
  const_unique_depth_iteratort unique_depth_begin() const;
  const_unique_depth_iteratort unique_depth_end() const;
  const_unique_depth_iteratort unique_depth_cbegin() const;
  const_unique_depth_iteratort unique_depth_cend() const;
};

class expr_visitort
{
public:
  virtual ~expr_visitort() { }
  virtual void operator()(exprt &) { }
};

class const_expr_visitort
{
public:
  virtual ~const_expr_visitort() { }
  virtual void operator()(const exprt &) { }
};

#endif // CPROVER_UTIL_EXPR_H
