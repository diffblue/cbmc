/*******************************************************************\

Module: Constant propagation

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Constant propagation
///
/// A simple, unsound constant propagator. Assignments to symbols (local and
/// global variables) are tracked, and propagated if a unique value is found
/// at a given use site. Function calls are accounted for (they are assumed to
/// overwrite all address-taken variables; see \ref dirtyt), but assignments
/// through pointers are not (they are assumed to have no effect).
///
/// Can be restricted to operate over only particular symbols by passing a
/// predicate to a \ref constant_propagator_ait constructor, in which case this
/// can be rendered sound by restricting it to non-address-taken variables.

#ifndef CPROVER_ANALYSES_CONSTANT_PROPAGATOR_H
#define CPROVER_ANALYSES_CONSTANT_PROPAGATOR_H

#include <iosfwd>
#include <util/replace_symbol.h>

#include "ai.h"
#include "dirty.h"

class constant_propagator_ait;

class constant_propagator_domaint:public ai_domain_baset
{
public:
  virtual void transform(
    const irep_idt &function_from,
    locationt from,
    const irep_idt &function_to,
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
    // maps variables to constants
    address_of_aware_replace_symbolt replace_const;
    bool is_bottom = true;

    bool merge(const valuest &src);
    bool meet(const valuest &src, const namespacet &ns);

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

    void set_to(const symbol_exprt &lhs, const exprt &rhs)
    {
      replace_const.set(lhs, rhs);
      is_bottom=false;
    }

    bool set_to_top(const symbol_exprt &expr);

    void set_dirty_to_top(const dirtyt &dirty, const namespacet &ns);

    bool is_constant(const exprt &expr) const;
    bool is_array_constant(const exprt &expr) const;
    bool is_constant_address_of(const exprt &expr) const;

    bool is_empty() const
    {
      return replace_const.empty();
    }

    void output(std::ostream &out, const namespacet &ns) const;
  };

  valuest values;

  bool partial_evaluate(exprt &expr, const namespacet &ns) const;

protected:
  void assign_rec(
    valuest &values,
    const exprt &lhs,
    const exprt &rhs,
    const namespacet &ns,
    const constant_propagator_ait *cp);

  bool two_way_propagate_rec(
    const exprt &expr,
    const namespacet &ns,
    const constant_propagator_ait *cp);

  bool partial_evaluate_with_all_rounding_modes(
    exprt &expr,
    const namespacet &ns) const;

  bool replace_constants_and_simplify(exprt &expr, const namespacet &ns) const;
};

class constant_propagator_ait:public ait<constant_propagator_domaint>
{
public:
  typedef std::function<bool(const exprt &, const namespacet &)>
    should_track_valuet;

  static bool track_all_values(const exprt &, const namespacet &)
  {
    return true;
  }

  explicit constant_propagator_ait(
    const goto_functionst &goto_functions,
    should_track_valuet should_track_value = track_all_values):
    dirty(goto_functions),
    should_track_value(should_track_value)
  {
  }

  explicit constant_propagator_ait(
    const goto_functiont &goto_function,
    should_track_valuet should_track_value = track_all_values):
    dirty(goto_function),
    should_track_value(should_track_value)
  {
  }

  constant_propagator_ait(
    goto_modelt &goto_model,
    should_track_valuet should_track_value = track_all_values):
    dirty(goto_model.goto_functions),
    should_track_value(should_track_value)
  {
    const namespacet ns(goto_model.symbol_table);
    operator()(goto_model.goto_functions, ns);
    replace(goto_model.goto_functions, ns);
  }

  constant_propagator_ait(
    const irep_idt &function_identifier,
    goto_functionst::goto_functiont &goto_function,
    const namespacet &ns,
    should_track_valuet should_track_value = track_all_values)
    : dirty(goto_function), should_track_value(should_track_value)
  {
    operator()(function_identifier, goto_function, ns);
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

  should_track_valuet should_track_value;
};

#endif // CPROVER_ANALYSES_CONSTANT_PROPAGATOR_H
