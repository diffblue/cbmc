/*******************************************************************\

Module: Constant propagation

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_CONSTANT_PROPAGATOR_H
#define CPROVER_CONSTANT_PROPAGATOR_H

#include "ai.h"

#include "replace_symbol_ext.h"

class constant_propagator_domaint:public ai_domain_baset
{
public:
  virtual void transform(locationt, locationt, ai_baset &, const namespacet &);
  virtual void output(std::ostream &, const ai_baset &, const namespacet &) const;
  bool merge(const constant_propagator_domaint &, locationt, locationt);

  struct valuest
  {
  public:
    // maps variables to constants
    replace_symbol_extt replace_const;
    std::set<irep_idt> top_ids;
    
    void output(std::ostream &, const namespacet &) const;
    
    bool merge(const valuest &src);
    
    inline void clear()
    {
      replace_const.expr_map.clear();
      replace_const.type_map.clear();
      top_ids.clear();
    }
    
    bool empty() const
    {
      return replace_const.expr_map.empty() && 
	replace_const.type_map.empty() &&
	top_ids.empty();
    }

    void set_to(const exprt &lhs, const exprt &rhs_val);
    void set_to(const irep_idt &lhs_id, const exprt &rhs_val);
    
    bool is_constant(const exprt &expr) const;
    bool is_constant_address_of(const exprt &expr) const;
    bool set_to_top(const exprt &expr);
    bool set_to_top(const irep_idt &id);
    void set_all_to_top();
  };

  valuest values;
  
protected:
  void assign(
    valuest &dest,
    const exprt &lhs,
    exprt rhs,
    const namespacet &ns) const;

  void assign_rec(valuest &values,
		  const exprt &lhs, const exprt &rhs,
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

#endif
