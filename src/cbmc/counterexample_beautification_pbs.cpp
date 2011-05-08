/*******************************************************************\

Module: Counterexample Beautification using PBS

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <bitvector.h>
#include <expr_util.h>
#include <arith_tools.h>

#include "counterexample_beautification_pbs.h"

/*******************************************************************\

Function: counterexample_beautification_pbst::beautify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_pbst::beautify(
  pbs_dimacs_cnft &pbs,
  bv_cbmct &bv_cbmc,
  const namespacet &ns,
  const exprt &expr,
  const typet &type,
  unsigned offset)
{
  // array or struct?

  if(type.id()=="array")
  {
    // get size
    const exprt &size_expr=(exprt &)type.find("size");
    mp_integer size_int, i;

    if(to_integer(size_expr, size_int)) return;

    boolbv_widtht boolbv_width(ns);

    // get element width
    unsigned width=boolbv_width(type.subtype());

    if(width==0)
      return;

    for(i=0; i<size_int; ++i)
    {
      beautify(pbs, bv_cbmc, ns, expr, type.subtype(), offset);
      offset+=width;
    }    
  }
  else if(type.id()=="struct")
  {
    const irept::subt &components=type.find("components").get_sub();

    boolbv_widtht boolbv_width(ns);
  
    forall_irep(it, components)
    {
      const typet &subtype=(typet &)it->find("type");
      unsigned width=boolbv_width(subtype);

      if(width==0) continue;

      beautify(pbs, bv_cbmc, ns, expr, subtype, offset);

      offset+=width;
    }
  }
  else if(type.id()=="symbol")
  {
    const symbolt &s=ns.lookup(type.get("identifier"));
    beautify(pbs, bv_cbmc, ns, expr, s.type, offset);
  }
  else if(type.id()=="pointer")
  {
    // no beautification for pointers right now
  }
  else if(type.id()=="signedbv" ||
          type.id()=="unsignedbv")
  {
    bool is_signed=type.id()=="signedbv";

    boolbv_widtht boolbv_width(ns);

    unsigned width=boolbv_width(type);
    
    for(unsigned i=0; i<width; i++)
    {
      unsigned bit=offset+i;

      literalt l;
      if(bv_cbmc.literal(expr, bit, l))
        continue;

      unsigned long weight=(1L<<i);

      if(is_signed)
      {
        if(i==(width-1)) // sign bit?
          weight=1;
        else
        {
          // get the sign bit literal

          literalt sign_bit;
          if(bv_cbmc.literal(expr, offset+width-1, sign_bit))
            continue;

          l=pbs.lxor(l, sign_bit);
        }
      }

      pbs.pb_constraintmap[l]=weight;
    }
  }
}

/*******************************************************************\

Function: counterexample_beautification_pbst::counterexample_beautification_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_pbst::counterexample_beautification_values(
  cnf_clause_listt &cnf,
  bv_cbmct &bv_cbmc,
  symex_target_equationt &equation,
  const namespacet &ns)
{
  // get symbols we care about
  minimization_symbolst minimization_symbols;

  get_minimization_symbols(bv_cbmc, equation, failed, minimization_symbols);

  pbs_dimacs_cnft pbs_solver;
  setup_pbs(cnf, pbs_solver);

  // assign weights
  for(minimization_symbolst::const_iterator it=minimization_symbols.begin();
      it!=minimization_symbols.end(); it++)
    beautify(pbs_solver, bv_cbmc, ns, *it, (*it).type(), 0);

  // lock the guards
  for(guard_constraintst::const_iterator
      it=guard_constraints.begin();
      it!=guard_constraints.end();
      it++)
    pbs_solver.lcnf(*it);

  run_pbs(pbs_solver);

  // copy satisfying assignment
  cnf.copy_assignment_from(pbs_solver);

  // check the guards

  for(guard_constraintst::const_iterator
      it=guard_constraints.begin();
      it!=guard_constraints.end();
      it++)
    if(it->size()==1)
    {
      tvt value=pbs_solver.l_get(it->front());
      assert(value.is_true());
    }

  #if 0
  unsigned states=0;

  for(symex_target_equationt::statest::const_iterator
      it=bv_cbmc.bmc.equation.states.begin();
      it!=bv_cbmc.bmc.equation.states.end(); it++)
    if(it->symbol!="")
    {
      tvt value=pbs_solver.l_get(it->guard_literal);
      assert(!value.is_unknown());
      if(value.is_true()) states++;
    }

  std::cout << "DEBUG 1 " << states << std::endl;
  #endif
}

/*******************************************************************\

Function: counterexample_beautification_pbst::counterexample_beautification_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_pbst::counterexample_beautification_guards(
  cnf_clause_listt &cnf,
  bv_cbmct &bv_cbmc,
  symex_target_equationt &equation,
  const namespacet &ns)
{
  typedef std::map<literalt, unsigned> guard_countt;
  guard_countt guard_count;

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
  {
    if(it->is_assignment() &&
       it->assignment_type!=symex_targett::HIDDEN)
    {
      if(it->guard_literal!=const_literal(false) &&
         it->guard_literal!=const_literal(true))
        guard_count[it->guard_literal]++;
    }

    // reached failed assertion?
    if(it==failed)
      break;
  }

  pbs_dimacs_cnft pbs_solver;
  setup_pbs(cnf, pbs_solver);

  // one of the assertions up to the failed
  // assertion must fail
  {
    bvt assertion_clause;

    for(symex_target_equationt::SSA_stepst::const_iterator
        it=equation.SSA_steps.begin();
        it!=equation.SSA_steps.end(); it++)
    {
      if(it->is_assert())
        assertion_clause.push_back(pbs_solver.lnot(it->cond_literal));

      if(it==failed) break;
    }

    guard_constraints.push_back(assertion_clause);
    pbs_solver.lcnf(assertion_clause);
  }

  // assign weights

  for(guard_countt::const_iterator
      it=guard_count.begin();
      it!=guard_count.end();
      it++)
    pbs_solver.pb_constraintmap[it->first]=it->second;

  run_pbs(pbs_solver);

  // copy satisfying assignment
  cnf.copy_assignment_from(pbs_solver);

  // lock the guards in place
  for(guard_countt::const_iterator
      it=guard_count.begin();
      it!=guard_count.end();
      it++)
  {
    literalt l=it->first;
    tvt value=pbs_solver.l_get(l);
    assert(!value.is_unknown());
    bvt clause;
    clause.push_back(value.is_true()?l:cnf.lnot(l));   
    guard_constraints.push_back(clause);
  }
}

/*******************************************************************\

Function: counterexample_beautification_pbst::counterexample_beautification

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_pbst::counterexample_beautification(
  cnf_clause_listt &cnf,
  bv_cbmct &bv_cbmc,
  symex_target_equationt &equation,
  const namespacet &ns)
{
  // find failed claim
  failed=get_failed_claim(bv_cbmc, equation);

  bv_cbmc.status("Beautifying Counterexample using PBS (Guards)");
  counterexample_beautification_guards(cnf, bv_cbmc, equation, ns);

  bv_cbmc.status("Beautifying Counterexample using PBS (Values)");
  counterexample_beautification_values(cnf, bv_cbmc, equation, ns);
}

/*******************************************************************\

Function: counterexample_beautification_pbst::setup_pbs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_pbst::setup_pbs(
  const cnf_clause_listt &cnf,
  pbs_dimacs_cnft &pbs)
{
  // copy clauses
  cnf.copy_to(pbs);

  pbs.optimize=true;
  pbs.binary_search=true;
  pbs.maximize=false;
  pbs.goal=0;
}

/*******************************************************************\

Function: counterexample_beautification_pbst::run_pbs

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_pbst::run_pbs(
  pbs_dimacs_cnft &pbs)
{
  if(pbs.prop_solve()!=propt::P_SATISFIABLE)
    throw "unexpected result from PBS";
}
