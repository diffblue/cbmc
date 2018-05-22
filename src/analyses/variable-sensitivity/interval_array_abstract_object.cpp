/*******************************************************************\

Module: analyses variable-sensitivity interval-values arrays

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/interval.h>
#include "abstract_enviroment.h"
#include "interval_array_abstract_object.h"

interval_array_abstract_objectt::interval_array_abstract_objectt(typet type) : constant_array_abstract_objectt(type) {

}

interval_array_abstract_objectt::interval_array_abstract_objectt(typet type, bool top, bool bottom)
  : constant_array_abstract_objectt(type, top, bottom) {

}

interval_array_abstract_objectt::interval_array_abstract_objectt(const exprt &expr,
                                                                 const abstract_environmentt &environment,
                                                                 const namespacet &ns)
  : constant_array_abstract_objectt(expr, environment, ns) {}

sharing_ptrt<array_abstract_objectt>
interval_array_abstract_objectt::write_index(abstract_environmentt &environment, const namespacet &ns,
                                             const std::stack<exprt> stack, const index_exprt &index_expr,
                                             const abstract_object_pointert value, bool merging_write) const {
  auto evaluated_index = environment.eval(index_expr.index(), ns);
  auto evaluated_index_const = evaluated_index->to_constant();
  if(evaluated_index_const.id() == ID_constant) {
    return constant_array_abstract_objectt::write_index(environment, ns, stack, index_expr, value, merging_write);
  } else if(evaluated_index_const.id() == ID_constant_interval) {
    auto const& index_interval = to_constant_interval_expr(evaluated_index_const);
    if(index_interval.is_single_value_interval()) {
      return constant_array_abstract_objectt::write_index(environment, ns, stack,
                                                          index_exprt(index_expr.array(), index_interval.get_lower()),
                                                          value, merging_write);
    }
    else if(!index_interval.is_top() && !index_interval.is_bottom()) {
      auto ix = index_interval.get_lower();
      auto interval_end = index_interval.get_upper();
      sharing_ptrt<abstract_objectt> result = shared_from_this();
      while(simplify_expr(binary_predicate_exprt(ix, ID_gt, interval_end), ns).is_false()) {
        auto array_after_write_at_index = constant_array_abstract_objectt::write_index(
          environment, ns, stack, index_exprt(index_expr.index(), ix), value, merging_write);
        bool dontcare;
        result = abstract_objectt::merge(result, array_after_write_at_index, dontcare);
        ix = simplify_expr(plus_exprt(ix, constant_exprt("1", ix.type())), ns);
      }
      return std::dynamic_pointer_cast<const array_abstract_objectt>(result);
    }
  }
  return std::dynamic_pointer_cast<const array_abstract_objectt>(make_top());
}

abstract_object_pointert
interval_array_abstract_objectt::read_index(const abstract_environmentt &env, const index_exprt &index,
                                            const namespacet &ns) const {
  auto evaluated_index = env.eval(index.index(), ns);
  auto evaluated_index_const = evaluated_index->to_constant();
  if(evaluated_index_const.id() == ID_constant) {
    UNREACHABLE;
    return constant_array_abstract_objectt::read_index(env,index,ns);
  } else if(evaluated_index_const.id() == ID_constant_interval) {
    auto const& index_interval = to_constant_interval_expr(evaluated_index_const);
    if(!index_interval.is_top() && !index_interval.is_bottom())
    {
      auto ix = index_interval.get_lower();
      auto interval_end = index_interval.get_upper();
      abstract_object_pointert value;
      while(simplify_expr(binary_relation_exprt(ix, ID_gt, interval_end), ns).is_false())
      {
        auto value_at_index = constant_array_abstract_objectt::read_index(env, index_exprt(index.array(), ix), ns);
        if(value != nullptr) {
          bool dont_care;
          value = abstract_objectt::merge(value, value_at_index, dont_care);
        } else {
          value = value_at_index;
        }
        ix = simplify_expr(plus_exprt(ix, constant_exprt("1", ix.type())), ns);
      }
      return value;
    }
  }
  return env.abstract_object_factory(type().subtype(), ns);
}

bool interval_array_abstract_objectt::eval_index(const index_exprt &index, const abstract_environmentt &env,
                                                 const namespacet &ns, mp_integer &out_index) const {
  auto index_value = env.eval(index.index(), ns);
  auto index_const = index_value->to_constant();
  if(index_const.id() != ID_constant_interval) {
    return constant_array_abstract_objectt::eval_index(index, env, ns, out_index);
  }
  auto index_interval = to_constant_interval_expr(index_const);
  if(index_interval.is_single_value_interval()) {
    out_index = numeric_cast_v<mp_integer>(index_interval.get_lower());
    return true;
  }
  return false;
}
