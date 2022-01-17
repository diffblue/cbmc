/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Jez Higgins, jez@jezuk.co.uk

\*******************************************************************/

/// \file
/// Common behaviour for abstract objects modelling aggregate values -
/// arrays, structs, etc.
#ifndef CBMC_ABSTRACT_AGGREGATE_OBJECT_H
#define CBMC_ABSTRACT_AGGREGATE_OBJECT_H

#include <analyses/variable-sensitivity/abstract_environment.h>
#include <analyses/variable-sensitivity/abstract_object.h>
#include <stack>

#include "abstract_object_statistics.h"

class abstract_aggregate_tag
{
};

template <class aggregate_typet, class aggregate_traitst>
class abstract_aggregate_objectt : public abstract_objectt,
                                   public abstract_aggregate_tag
{
public:
  explicit abstract_aggregate_objectt(const typet &type)
    : abstract_objectt(type)
  {
    PRECONDITION(type.id() == aggregate_traitst::TYPE_ID());
  }

  abstract_aggregate_objectt(const typet &type, bool tp, bool bttm)
    : abstract_objectt(type, tp, bttm)
  {
    PRECONDITION(type.id() == aggregate_traitst::TYPE_ID());
  }

  abstract_aggregate_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns)
    : abstract_objectt(expr, environment, ns)
  {
    PRECONDITION(ns.follow(expr.type()).id() == aggregate_traitst::TYPE_ID());
  }

  abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const override
  {
    if(expr.id() == aggregate_traitst::ACCESS_EXPR_ID())
      return read_component(environment, expr, ns);

    return abstract_objectt::expression_transform(
      expr, operands, environment, ns);
  }

  abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const override
  {
    return write_component(
      environment, ns, stack, specifier, value, merging_write);
  }

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override
  {
    abstract_objectt::get_statistics(statistics, visited, env, ns);
    aggregate_traitst::get_statistics(statistics, visited, env, ns);
    this->statistics(statistics, visited, env, ns);
  }

protected:
  virtual abstract_object_pointert read_component(
    const abstract_environmentt &environment,
    const exprt &expr,
    const namespacet &ns) const
  {
    // If we are bottom then so are the components
    // otherwise the components could be anything
    return environment.abstract_object_factory(
      aggregate_traitst::read_type(expr.type(), type()),
      ns,
      !is_bottom(),
      is_bottom());
  }

  virtual abstract_object_pointert write_component(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &expr,
    const abstract_object_pointert &value,
    bool merging_write) const
  {
    if(is_top() || is_bottom())
    {
      return shared_from_this();
    }
    else
    {
      return std::make_shared<aggregate_typet>(type(), true, false);
    }
  }

  virtual void statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const = 0;

  template <class keyt, typename hash>
  static bool merge_shared_maps(
    const sharing_mapt<keyt, abstract_object_pointert, false, hash> &map1,
    const sharing_mapt<keyt, abstract_object_pointert, false, hash> &map2,
    sharing_mapt<keyt, abstract_object_pointert, false, hash> &out_map,
    const widen_modet &widen_mode)
  {
    bool modified = false;

    typename sharing_mapt<keyt, abstract_object_pointert, false, hash>::
      delta_viewt delta_view;
    map1.get_delta_view(map2, delta_view, true);

    for(auto &item : delta_view)
    {
      auto v_new =
        abstract_objectt::merge(item.m, item.get_other_map_value(), widen_mode);
      if(v_new.modified)
      {
        modified = true;
        out_map.replace(item.k, v_new.object);
      }
    }

    return modified;
  }
};

struct array_aggregate_typet
{
  static const irep_idt TYPE_ID()
  {
    return ID_array;
  }
  static const irep_idt ACCESS_EXPR_ID()
  {
    return ID_index;
  }
  static typet read_type(const typet &, const typet &object_type)
  {
    array_typet array_type(to_array_type(object_type));
    return array_type.element_type();
  }

  static void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns)
  {
    ++statistics.number_of_arrays;
  }
};

struct struct_aggregate_typet
{
  static const irep_idt &TYPE_ID()
  {
    return ID_struct;
  }
  static const irep_idt &ACCESS_EXPR_ID()
  {
    return ID_member;
  }
  static const typet &read_type(const typet &expr_type, const typet &)
  {
    return expr_type;
  }

  static void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns)
  {
    ++statistics.number_of_structs;
  }
};

struct union_aggregate_typet
{
  static const irep_idt TYPE_ID()
  {
    return ID_union;
  }
  static const irep_idt ACCESS_EXPR_ID()
  {
    return ID_member;
  }
  static typet read_type(const typet &, const typet &object_type)
  {
    return object_type;
  }

  static void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns)
  {
  }
};

#endif //CBMC_ABSTRACT_AGGREGATE_OBJECT_H
