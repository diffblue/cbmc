/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_EXPR_H
#define CPROVER_UTIL_EXPR_H

#include "as_const.h"
#include "type.h"
#include "validate_expressions.h"
#include "validate_types.h"
#include "validation_mode.h"

#include <functional>

#define forall_operands(it, expr)                                              \
  for(exprt::operandst::const_iterator                                         \
        it = as_const(expr).operands().begin(),                                \
        it##_end = as_const(expr).operands().end();                            \
      it != it##_end;                                                          \
      ++it)

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

  exprt(irep_idt _id, typet _type)
    : irept(std::move(_id), {{ID_type, std::move(_type)}}, {})
  {
  }

  exprt(irep_idt _id, typet _type, operandst &&_operands)
    : irept(
        std::move(_id),
        {{ID_type, std::move(_type)}},
        std::move((irept::subt &&) _operands))
  {
  }

  exprt(const irep_idt &id, typet type, source_locationt loc)
    : exprt(id, std::move(type))
  {
    add_source_location() = std::move(loc);
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

protected:
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

public:
  void reserve_operands(operandst::size_type n)
  { operands().reserve(n) ; }

  /// Copy the given argument to the end of `exprt`'s operands.
  /// \param expr: `exprt` to append to the operands
  void copy_to_operands(const exprt &expr)
  {
    operands().push_back(expr);
  }

  /// Add the given argument to the end of `exprt`'s operands.
  /// \param expr: `exprt` to append to the operands
  void add_to_operands(const exprt &expr)
  {
    copy_to_operands(expr);
  }

  /// Add the given argument to the end of `exprt`'s operands.
  /// \param expr: `exprt` to append to the operands
  void add_to_operands(exprt &&expr)
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

  /// Add the given arguments to the end of `exprt`'s operands.
  /// \param e1: first `exprt` to append to the operands
  /// \param e2: second `exprt` to append to the operands
  void add_to_operands(const exprt &e1, const exprt &e2)
  {
    copy_to_operands(e1, e2);
  }

  /// Add the given arguments to the end of `exprt`'s operands.
  /// \param e1: first `exprt` to append to the operands
  /// \param e2: second `exprt` to append to the operands
  void add_to_operands(exprt &&e1, exprt &&e2)
  {
    operandst &op = operands();
    #ifndef USE_LIST
    op.reserve(op.size() + 2);
    #endif
    op.push_back(std::move(e1));
    op.push_back(std::move(e2));
  }

  /// Add the given arguments to the end of `exprt`'s operands.
  /// \param e1: first `exprt` to append to the operands
  /// \param e2: second `exprt` to append to the operands
  /// \param e3: third `exprt` to append to the operands
  void add_to_operands(const exprt &e1, const exprt &e2, const exprt &e3)
  {
    copy_to_operands(e1, e2, e3);
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

  /// Add the given arguments to the end of `exprt`'s operands.
  /// \param e1: first `exprt` to append to the operands
  /// \param e2: second `exprt` to append to the operands
  /// \param e3: third `exprt` to append to the operands
  void add_to_operands(exprt &&e1, exprt &&e2, exprt &&e3)
  {
    operandst &op = operands();
    #ifndef USE_LIST
    op.reserve(op.size() + 3);
    #endif
    op.push_back(std::move(e1));
    op.push_back(std::move(e2));
    op.push_back(std::move(e3));
  }

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

  void drop_source_location()
  {
    remove(ID_C_source_location);
  }

  /// Check that the expression is well-formed (shallow checks only, i.e.,
  /// subexpressions and its type are not checked).
  ///
  /// Subclasses may override this function to provide specific well-formedness
  /// checks for the corresponding expressions.
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  static void check(const exprt &, const validation_modet)
  {
  }

  /// Check that the expression is well-formed, assuming that its subexpressions
  /// and type have all ready been checked for well-formedness.
  ///
  /// Subclasses may override this function to provide specific well-formedness
  /// checks for the corresponding expressions.
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  static void validate(
    const exprt &expr,
    const namespacet &,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    check_expr(expr, vm);
  }

  /// Check that the expression is well-formed (full check, including checks
  /// of all subexpressions and the type)
  ///
  /// Subclasses may override this function, though in most cases the provided
  /// implementation should be sufficient.
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  static void validate_full(
    const exprt &expr,
    const namespacet &ns,
    const validation_modet vm = validation_modet::INVARIANT)
  {
    // first check operands (if any)
    for(const exprt &op : expr.operands())
    {
      validate_full_expr(op, ns, vm);
    }

    // type may be nil
    const typet &t = expr.type();

    validate_full_type(t, ns, vm);

    validate_expr(expr, ns, vm);
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
  /// These are pre-order traversal visitors, i.e.,
  /// the visitor is executed on a node _before_ its children
  /// have been visited.
  void visit(class expr_visitort &visitor);
  void visit(class const_expr_visitort &visitor) const;
  void visit_pre(std::function<void(exprt &)>);
  void visit_pre(std::function<void(const exprt &)>) const;

  /// These are post-order traversal visitors, i.e.,
  /// the visitor is executed on a node _after_ its children
  /// have been visited.
  void visit_post(std::function<void(exprt &)>);
  void visit_post(std::function<void(const exprt &)>) const;

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

/// Base class for all expressions. This protects low-level methods in
/// exprt that are not type safe. Depcrecated constructors are removed.
/// This API will eventually replace exprt.
class expr_protectedt : public exprt
{
protected:
  // constructors
  expr_protectedt(irep_idt _id, typet _type)
    : exprt(std::move(_id), std::move(_type))
  {
  }

  expr_protectedt(irep_idt _id, typet _type, operandst _operands)
    : exprt(std::move(_id), std::move(_type), std::move(_operands))
  {
  }

  // protect these low-level methods
  using exprt::add;
  using exprt::op0;
  using exprt::op1;
  using exprt::op2;
  using exprt::op3;
  using exprt::remove;
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
