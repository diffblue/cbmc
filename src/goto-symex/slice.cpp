/*******************************************************************\

Module: Slicer for symex traces

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Slicer for symex traces

#include "slice.h"

#include <util/std_expr.h>

#include "symex_slice_class.h"

static void get_symbols(const typet &type, symbol_sett &depends)
{
  // TODO
}

static void get_symbols(const exprt &expr, symbol_sett &depends)
{
  get_symbols(expr.type(), depends);

  forall_operands(it, expr)
    get_symbols(*it, depends);

  if(expr.id()==ID_symbol)
    depends.insert(to_symbol_expr(expr).get_identifier());
}

namespace
{

class slicing_visitort : public SSA_const_visitor
{
public:
  explicit slicing_visitort(symbol_sett &depends) : depends_{depends}
  {
  }

  void visit(SSA_assertt &x) const
  {
    get_symbols(x.cond_expr, depends_);
  }

  void visit(SSA_assumet &x) const
  {
    get_symbols(x.cond_expr, depends_);
  }

  void visit(SSA_assignmentt &x) const
  {
    assert(x.ssa_lhs.id() == ID_symbol);
    const irep_idt &id = x.ssa_lhs.get_identifier();

    if(depends_.find(id) == depends_.end())
    {
      // we don't really need it
      x.ignore = true;
    }
    else
      get_symbols(x.ssa_rhs, depends_);
  }

  void visit(SSA_gotot &x) const
  {
    get_symbols(x.cond_expr, depends_);
  }

  void visit(SSA_constraintt &x) const
  {
  }

  void visit(SSA_locationt &x) const
  {
  }

  void visit(SSA_outputt &x) const
  {
  }

  void visit(SSA_declt &x) const
  {
    assert(x.ssa_lhs.id() == ID_symbol);
    const irep_idt &id = x.ssa_lhs.get_identifier();

    if(depends_.find(id) == depends_.end())
    {
      // we don't really need it
      x.ignore = true;
    }
  }

  void visit(SSA_function_callt &x) const
  {
  }

  void visit(SSA_function_returnt &x) const
  {
  }

  void visit(SSA_shared_readt &x) const
  {
  }

  void visit(SSA_shared_writet &x) const
  {
  }

  void visit(SSA_spawnt &x) const
  {
  }

  void visit(SSA_memory_barriert &x) const
  {
  }

  void visit(SSA_atomic_begint &x) const
  {
  }

  void visit(SSA_atomic_endt &x) const
  {
  }

  void visit(SSA_inputt &x) const
  {
  }

private:
  symbol_sett &depends_;
};

class collecting_visitort : public SSA_const_visitor_const_args
{
public:
  explicit collecting_visitort(symbol_sett &depends, symbol_sett &lhs)
    : depends_{depends}, lhs_{lhs}
  {
  }

  void visit(const SSA_assertt &x) const
  {
    get_symbols(x.cond_expr, depends_);
  }

  void visit(const SSA_assumet &x) const
  {
    get_symbols(x.cond_expr, depends_);
  }

  void visit(const SSA_assignmentt &x) const
  {
    get_symbols(x.ssa_rhs, depends_);
    lhs_.insert(x.ssa_lhs.get_identifier());
  }

  void visit(const SSA_gotot &x) const
  {
  }

  void visit(const SSA_constraintt &x) const
  {
  }

  void visit(const SSA_locationt &x) const
  {
  }

  void visit(const SSA_outputt &x) const
  {
  }

  void visit(const SSA_declt &x) const
  {
  }

  void visit(const SSA_function_callt &x) const
  {
  }

  void visit(const SSA_function_returnt &x) const
  {
  }

  void visit(const SSA_shared_readt &x) const
  {
  }

  void visit(const SSA_shared_writet &x) const
  {
  }

  void visit(const SSA_spawnt &x) const
  {
  }

  void visit(const SSA_memory_barriert &x) const
  {
  }

  void visit(const SSA_atomic_begint &x) const
  {
  }

  void visit(const SSA_atomic_endt &x) const
  {
  }

  void visit(const SSA_inputt &x) const
  {
  }

private:
  symbol_sett &depends_;
  symbol_sett &lhs_;
};

} // namespace

void symex_slicet::slice(
  symex_target_equationt &equation,
  const expr_listt &exprs)
{
  // collect dependencies
  forall_expr_list(expr_it, exprs)
    get_symbols(*expr_it, depends_);

  slice(equation);
}

void symex_slicet::slice(symex_target_equationt &equation)
{
  for(symex_target_equationt::SSA_stepst::reverse_iterator
      it=equation.SSA_steps.rbegin();
      it!=equation.SSA_steps.rend();
      it++)
    slice(**it);
}

void symex_slicet::slice(symex_target_equationt::SSA_stept &SSA_step)
{
  get_symbols(SSA_step.guard, depends_);
  SSA_step.accept(slicing_visitort{depends_});
}

/// Collect the open variables, i.e., variables that are used in RHS but never
/// written in LHS
/// \param equation: symex trace
/// \param open_variables: target set
/// \return None. But open_variables is modified as a side-effect.
void symex_slicet::collect_open_variables(
  const symex_target_equationt &equation,
  symbol_sett &open_variables)
{
  symbol_sett lhs;

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
  {
    const symex_target_equationt::SSA_stept &SSA_step=**it;

    get_symbols(SSA_step.guard, depends_);
    SSA_step.accept(collecting_visitort{depends_, lhs});
  }

  open_variables=depends_;

  // remove the ones that are defined
  open_variables.erase(lhs.begin(), lhs.end());
}

void slice(symex_target_equationt &equation)
{
  symex_slicet symex_slice;
  symex_slice.slice(equation);
}

/// Collect the open variables, i.e. variables that are used in RHS but never
/// written in LHS
/// \param equation: symex trace
/// \param open_variables: target set
/// \return None. But open_variables is modified as a side-effect.
void collect_open_variables(
  const symex_target_equationt &equation,
  symbol_sett &open_variables)
{
  symex_slicet symex_slice;
  symex_slice.collect_open_variables(equation, open_variables);
}

/// Slice the symex trace with respect to a list of expressions
/// \param equation: symex trace to be sliced
/// \param expression: list of expressions, targets for slicing
/// \return None. But equation is modified as a side-effect.
void slice(symex_target_equationt &equation,
           const expr_listt &expressions)
{
  symex_slicet symex_slice;
  symex_slice.slice(equation, expressions);
}

void simple_slice(symex_target_equationt &equation)
{
  // just find the last assertion
  symex_target_equationt::SSA_stepst::iterator
    last_assertion=equation.SSA_steps.end();

  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
    if((*it)->is_assert())
      last_assertion=it;

  // slice away anything after it

  symex_target_equationt::SSA_stepst::iterator s_it=
    last_assertion;

  if(s_it!=equation.SSA_steps.end())
  {
    for(s_it++;
        s_it!=equation.SSA_steps.end();
        s_it++)
      (*s_it)->ignore=true;
  }
}
