/*******************************************************************\

Module: Constant propagation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Constant propagation

#ifndef CPROVER_ANALYSES_CONSTANT_PROPAGATOR_H
#define CPROVER_ANALYSES_CONSTANT_PROPAGATOR_H

#include "ai.h"

#include "replace_symbol_ext.h"

class constant_propagator_domaint:public ai_domain_baset
{
public:
  void transform(
    locationt,
    locationt,
    ai_baset &,
    const namespacet &) final;
  void output(
    std::ostream &,
    const ai_baset &,
    const namespacet &) const final;
  void make_top() final { values.set_to_top(); }
  void make_bottom() final { values.set_to_bottom(); }
  void make_entry() final { values.set_to_top(); }
  bool merge(const constant_propagator_domaint &, locationt, locationt);

  virtual bool ai_simplify(
    exprt &condition,
    const namespacet &ns) const override;

  struct valuest
  {
  public:
    valuest():is_bottom(true) { }

    // maps variables to constants
    replace_symbol_extt replace_const;
    bool is_bottom;

    void output(std::ostream &, const namespacet &) const;

    bool merge(const valuest &src);
    bool meet(const valuest &src);

    void set_to_bottom()
    {
      replace_const.clear();
      is_bottom = true;
    }

    void set_to(const irep_idt &lhs_id, const exprt &rhs_val)
    {
      replace_const.expr_map[lhs_id] = rhs_val;
      is_bottom = false;
    }

    void set_to(const symbol_exprt &lhs, const exprt &rhs_val)
    {
      set_to(lhs.get_identifier(), rhs_val);
    }

    bool is_constant(const exprt &expr) const;
    bool is_array_constant(const exprt &expr) const;
    bool is_constant_address_of(const exprt &expr) const;
    bool set_to_top(const irep_idt &id);

    bool set_to_top(const symbol_exprt &expr)
    {
      return set_to_top(expr.get_identifier());
    }

    void set_to_top()
    {
      replace_const.clear();
      is_bottom = false;
    }

  };

  valuest values;

private:
  void assign(
    valuest &dest,
    const symbol_exprt &lhs,
    exprt rhs,
    const namespacet &ns) const;

  void assign_rec(
    valuest &values,
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns);

  bool two_way_propagate_rec(
    const exprt &expr,
    const namespacet &ns);
};

class constant_propagator_ait:public ait<constant_propagator_domaint>
{
public:
  constant_propagator_ait(
    goto_functionst &goto_functions,
    const namespacet &ns)
  {
    operator()(goto_functions, ns);
    replace(goto_functions, ns);
  }

  constant_propagator_ait(
    goto_functionst::goto_functiont &goto_function,
    const namespacet &ns)
  {
    operator()(goto_function, ns);
    replace(goto_function, ns);
  }

protected:
  friend class constant_propagator_domaint;

  void replace_array_symbol(
		  exprt &expr);

  void replace(
    goto_functionst::goto_functiont &,
    const namespacet &);

  void replace(
    goto_functionst &,
    const namespacet &);

  void replace_types_rec(
    const replace_symbolt &replace_const,
    exprt &expr);

};

#endif // CPROVER_ANALYSES_CONSTANT_PROPAGATOR_H
