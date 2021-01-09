#ifndef CBMC_ABSTRACT_AGGREGATE_OBJECT_H
#define CBMC_ABSTRACT_AGGREGATE_OBJECT_H

#include <analyses/variable-sensitivity/abstract_object.h>
#include <analyses/variable-sensitivity/abstract_environment.h>
#include <stack>

class member_exprt;

class abstract_aggregate_tag { };

template<class aggregate_typet, class aggregate_traitst>
class abstract_aggregate_objectt :
  public abstract_objectt,
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
    if (expr.id() == aggregate_traitst::ACCESS_EXPR_ID())
      return read_component(environment, expr, ns);

    return abstract_objectt::expression_transform(
      expr, operands, environment, ns);
  }

  abstract_object_pointert write(
    abstract_environmentt& environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const override {
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
};

#endif //CBMC_ABSTRACT_AGGREGATE_OBJECT_H
