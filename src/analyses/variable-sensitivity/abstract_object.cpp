/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <iostream>

#include <analyses/variable-sensitivity/abstract_environment.h>

#include <util/mathematical_types.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include "abstract_object.h"

abstract_objectt::abstract_objectt(const typet &type)
  : t(type), bottom(false), top(true)
{
}

abstract_objectt::abstract_objectt(const typet &type, bool top, bool bottom)
  : t(type), bottom(bottom), top(top)
{
  PRECONDITION(!(top && bottom));
}

abstract_objectt::abstract_objectt(
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : t(expr.type()), bottom(false), top(true)
{
}

abstract_objectt::abstract_objectt(
  const typet &type,
  const exprt &expr,
  const abstract_environmentt &environment,
  const namespacet &ns)
  : t(type), bottom(false), top(true)
{
}

const typet &abstract_objectt::type() const
{
  return t;
}

abstract_object_pointert abstract_objectt::merge(
  const abstract_object_pointert &other,
  const widen_modet &widen_mode) const
{
  return abstract_object_merge(other);
}

abstract_object_pointert abstract_objectt::abstract_object_merge(
  const abstract_object_pointert &other) const
{
  if(is_top() || other->bottom)
    return this->abstract_object_merge_internal(other);

  internal_abstract_object_pointert merged = mutable_clone();
  merged->set_top();
  merged->bottom = false;
  return merged->abstract_object_merge_internal(other);
}

abstract_object_pointert abstract_objectt::abstract_object_merge_internal(
  const abstract_object_pointert &other) const
{
  // Default implementation
  return shared_from_this();
}

abstract_object_pointert
abstract_objectt::meet(const abstract_object_pointert &other) const
{
  return abstract_object_meet(other);
}

abstract_object_pointert abstract_objectt::abstract_object_meet(
  const abstract_object_pointert &other) const
{
  if(is_top())
    return other;

  if(is_bottom() || other->top)
    return this->abstract_object_meet_internal(other);

  internal_abstract_object_pointert met = mutable_clone();
  met->bottom = true;
  met->top = false;
  return met->abstract_object_meet_internal(other);
}

abstract_object_pointert abstract_objectt::abstract_object_meet_internal(
  const abstract_object_pointert &other) const
{
  // Default implementation
  return shared_from_this();
}

static bool is_pointer_addition(const exprt &expr)
{
  return (expr.id() == ID_plus) && (expr.type().id() == ID_pointer) &&
         (expr.operands().size() == 2) && is_number(expr.operands()[1].type());
}

abstract_object_pointert abstract_objectt::expression_transform(
  const exprt &expr,
  const std::vector<abstract_object_pointert> &operands,
  const abstract_environmentt &environment,
  const namespacet &ns) const
{
  exprt copy = expr;

  for(exprt &op : copy.operands())
  {
    abstract_object_pointert op_abstract_object = environment.eval(op, ns);
    const exprt &const_op = op_abstract_object->to_constant();
    op = const_op.is_nil() ? op : const_op;
  }

  if(!is_pointer_addition(copy))
    copy = simplify_expr(copy, ns);

  for(const exprt &op : copy.operands())
  {
    abstract_object_pointert op_abstract_object = environment.eval(op, ns);
    const exprt &const_op = op_abstract_object->to_constant();

    if(const_op.is_nil())
    {
      return environment.abstract_object_factory(copy.type(), ns, true, false);
    }
  }

  return environment.abstract_object_factory(copy.type(), copy, ns);
}

abstract_object_pointert abstract_objectt::write(
  abstract_environmentt &environment,
  const namespacet &ns,
  const std::stack<exprt> &stack,
  const exprt &specifier,
  const abstract_object_pointert &value,
  bool merging_write) const
{
  return environment.abstract_object_factory(type(), ns, true, false);
}

bool abstract_objectt::is_top() const
{
  return top;
}

bool abstract_objectt::is_bottom() const
{
  return bottom;
}

bool abstract_objectt::verify() const
{
  return !(top && bottom);
}

exprt abstract_objectt::to_constant() const
{
  return nil_exprt();
}

void abstract_objectt::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(top)
  {
    out << "TOP";
  }
  else if(bottom)
  {
    out << "BOTTOM";
  }
  else
  {
    out << "Unknown";
  }
}

abstract_objectt::combine_result abstract_objectt::merge(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2,
  const widen_modet &widen_mode)
{
  abstract_object_pointert result = op1->should_use_base_merge(op2)
                                      ? op1->abstract_object_merge(op2)
                                      : op1->merge(op2, widen_mode);
  // If no modifications, we will return the original pointer
  return {result, result != op1};
}

bool abstract_objectt::should_use_base_merge(
  const abstract_object_pointert &other) const
{
  return is_top() || other->is_bottom() || other->is_top();
}

abstract_objectt::combine_result abstract_objectt::meet(
  const abstract_object_pointert &op1,
  const abstract_object_pointert &op2)
{
  abstract_object_pointert result = op1->should_use_base_meet(op2)
                                      ? op1->abstract_object_meet(op2)
                                      : op1->meet(op2);
  // If no modifications, we will return the original pointer
  return {result, result != op1};
}

bool abstract_objectt::should_use_base_meet(
  const abstract_object_pointert &other) const
{
  return is_bottom() || is_top() || other->is_bottom() || other->is_top();
}

abstract_object_pointert abstract_objectt::update_location_context(
  const locationst &locations,
  const bool update_sub_elements) const
{
  return shared_from_this();
}

void abstract_objectt::dump_map(
  std::ostream out,
  const abstract_objectt::shared_mapt &m)
{
  shared_mapt::viewt view;
  m.get_view(view);

  out << "{";
  bool first = true;
  for(auto &item : view)
  {
    out << (first ? "" : ", ") << item.first;
    first = false;
  }
  out << "}";
}

void abstract_objectt::dump_map_diff(
  std::ostream out,
  const abstract_objectt::shared_mapt &m1,
  const abstract_objectt::shared_mapt &m2)
{
  shared_mapt::delta_viewt delta_view;
  m1.get_delta_view(m2, delta_view, false);

  out << "DELTA{";
  bool first = true;
  for(auto &item : delta_view)
  {
    out << (first ? "" : ", ") << item.k << "=" << item.is_in_both_maps();
    first = false;
  }
  out << "}";
}

abstract_object_pointert abstract_objectt::unwrap_context() const
{
  return shared_from_this();
}

void abstract_objectt::get_statistics(
  abstract_object_statisticst &statistics,
  abstract_object_visitedt &visited,
  const abstract_environmentt &env,
  const namespacet &ns) const
{
  const auto &this_ptr = shared_from_this();
  PRECONDITION(visited.find(this_ptr) == visited.end());
  visited.insert(this_ptr);
}
