/*******************************************************************\

Module: Constant propagation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Constant propagation

#ifndef CPROVER_ANALYSES_CONSTANT_PROPAGATOR_H
#define CPROVER_ANALYSES_CONSTANT_PROPAGATOR_H

#include <iosfwd>
#include <util/replace_symbol.h>

#include "ai.h"
#include "dirty.h"

class constant_propagator_domaint:public ai_domain_baset
{
public:
  virtual void transform(
    locationt from,
    locationt to,
    ai_baset &ai_base,
    const namespacet &ns) final override;

  virtual void output(
    std::ostream &out,
    const ai_baset &ai_base,
    const namespacet &ns) const override;

  bool merge(
    const constant_propagator_domaint &other,
    locationt from,
    locationt to);

  virtual bool ai_simplify(
    exprt &condition,
    const namespacet &ns) const final override;

  virtual void make_bottom() final override
  {
    values.set_to_bottom();
  }

  virtual void make_top() final override
  {
    values.set_to_top();
  }

  virtual void make_entry() final override
  {
    make_top();
  }

  virtual bool is_bottom() const final override
  {
    return values.is_bot();
  }

  virtual bool is_top() const final override
  {
    return values.is_top();
  }

  struct valuest
  {
  public:
    valuest():is_bottom(true) {}

    // maps variables to constants
    replace_symbolt replace_const;
    bool is_bottom;

    bool merge(const valuest &src);
    bool meet(const valuest &src);

    // set whole state

    void set_to_bottom()
    {
      replace_const.clear();
      is_bottom=true;
    }

    void set_to_top()
    {
      replace_const.clear();
      is_bottom=false;
    }

    bool is_bot() const
    {
      return is_bottom && replace_const.empty();
    }

    bool is_top() const
    {
      return !is_bottom && replace_const.empty();
    }

    // set single identifier

    void set_to(const irep_idt &lhs, const exprt &rhs)
    {
      replace_const.expr_map[lhs]=rhs;
      is_bottom=false;
    }

    void set_to(const symbol_exprt &lhs, const exprt &rhs)
    {
      set_to(lhs.get_identifier(), rhs);
    }

    bool set_to_top(const symbol_exprt &expr)
    {
      return set_to_top(expr.get_identifier());
    }

    bool set_to_top(const irep_idt &id);

    void set_dirty_to_top(const dirtyt &dirty, const namespacet &ns);

    bool is_constant(const exprt &expr) const;
    bool is_array_constant(const exprt &expr) const;
    bool is_constant_address_of(const exprt &expr) const;

    bool is_empty() const
    {
      assert(replace_const.type_map.empty());
      return replace_const.expr_map.empty();
    }

    void output(std::ostream &out, const namespacet &ns) const;
  };

  valuest values;

protected:
  void assign_rec(
    valuest &values,
    const exprt &lhs, const exprt &rhs,
    const namespacet &ns);

  bool two_way_propagate_rec(
    const exprt &expr,
    const namespacet &ns);
};

class constant_propagator_ait:public ait<constant_propagator_domaint>
{
public:
  explicit constant_propagator_ait(const goto_functionst &goto_functions):
    dirty(goto_functions)
  {
  }

  constant_propagator_ait(
    goto_functionst &goto_functions,
    const namespacet &ns):dirty(goto_functions)
  {
    operator()(goto_functions, ns);
    replace(goto_functions, ns);
  }

  constant_propagator_ait(
    goto_functionst::goto_functiont &goto_function,
    const namespacet &ns):dirty(goto_function)
  {
    operator()(goto_function, ns);
    replace(goto_function, ns);
  }

  dirtyt dirty;

protected:
  friend class constant_propagator_domaint;

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
