/*******************************************************************\

Module: Counterexample Beautification using Incremental SAT

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>

#include <bitvector.h>
#include <expr_util.h>
#include <arith_tools.h>
#include <symbol.h>

#include "counterexample_beautification_greedy.h"

/*******************************************************************\

Function: counterexample_beautification_greedyt::beautify_try

  Inputs:

 Outputs:

 Purpose: try specific assignment v to literal l

\*******************************************************************/

void counterexample_beautification_greedyt::beautify_try(
  solvert &solver,
  literalt l,
  bool v)
{
  if(solver.l_get(l)==tvt(v))
  {
    // already ok, but fix it
    solver.l_set_to(l, v);
    //std::cout << "ALREADY OK\n";
    return;
  }

  // won't change if constant  
  if(l.is_constant()) return;

  literalt clause_lit(l);
  if(!v) clause_lit=solver.lnot(clause_lit);

  bvt constraints;
  constraints.push_back(clause_lit);
  solver.set_assumptions(constraints);

  // save assignment, in case we get UNSAT
  save_assignment(solver);

  if(solver.prop_solve()==propt::P_SATISFIABLE)
  {
    // make this permanent
    solver.l_set_to(l, v);
    //std::cout << "SAT!\n";
  }
  else
  {
    //std::cout << "UNSAT!\n";

    // restore the assignment
    restore_assignment(solver);
  }
}

/*******************************************************************\

Function: counterexample_beautification_greedyt::minimize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_greedyt::minimize(
  solvert &solver,
  bv_cbmct &bv_cbmc,
  const namespacet &ns,
  const exprt &expr,
  const typet &type,
  unsigned offset,
  unsigned bit_nr) // starting from _most_ significant bit
{
  // array or struct?

  if(type.id()==ID_array)
  {
    // get size
    const exprt &size_expr=to_array_type(type).size();
    mp_integer size_int, i;

    if(to_integer(size_expr, size_int)) return;

    boolbv_widtht boolbv_width(ns);

    // get element width
    unsigned width=boolbv_width(type.subtype());

    if(width==0)
      return;

    for(i=0; i<size_int; ++i)
    {
      minimize(solver, bv_cbmc, ns, expr, type.subtype(), offset, bit_nr);
      offset+=width;
    }    
  }
  else if(type.id()==ID_struct)
  {
    const irept::subt &components=
      type.find(ID_components).get_sub();

    boolbv_widtht boolbv_width(ns);

    forall_irep(it, components)
    {
      const typet &subtype=
        static_cast<const typet &>(it->find(ID_type));

      unsigned width=boolbv_width(subtype);

      if(width==0) continue;

      minimize(solver, bv_cbmc, ns, expr, subtype, offset, bit_nr);

      offset+=width;
    }
  }
  else if(type.id()==ID_symbol)
  {
    const symbolt &s=ns.lookup(type.get(ID_identifier));
    minimize(solver, bv_cbmc, ns, expr, s.type, offset, bit_nr);
  }
  else if(type.id()==ID_pointer)
  {
    // no beautification for pointers right now
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv)
  {
    boolbv_widtht boolbv_width(ns);
  
    unsigned width=boolbv_width(type);

    if(bit_nr>=width) return;

    unsigned bit=offset+width-bit_nr-1;

    // std::cout << "XX: " << expr.get(ID_identifier)
    //           << " bit=" << bit_nr <<std::endl;

    if(type.id()==ID_signedbv) // signed?
    {
      if(bit_nr==0) // is it the sign bit?
      {
        literalt l;
        if(!bv_cbmc.literal(expr, bit, l))
          beautify_try(solver, l, false);
      }
      else
      {
        // try to get the sign bit
        literalt sign_l;
        if(bv_cbmc.literal(expr, offset+width-1, sign_l))
          return;

        bool want=(solver.l_get(sign_l).is_true());

        // see if we think it is worth it
        for(unsigned b=offset+width-2; b!=bit; b--)
        {
          literalt other_l;
          if(bv_cbmc.literal(expr, offset+width-1, other_l))
            return;

          if(solver.l_get(other_l)==tvt(!want))
            return;
        }

        literalt l;
        if(!bv_cbmc.literal(expr, bit, l))
          beautify_try(solver, l, want);
      }

    }
    else // unsigned
    {
      // see if we think it is worth it
      for(unsigned b=offset+width-1; b!=bit; b--)
      {
        literalt other_l;

        if(bv_cbmc.literal(expr, offset+width-1, other_l))
          return;

        if(solver.l_get(other_l).is_true())
          return;
      }

      literalt l;
      if(!bv_cbmc.literal(expr, bit, l))
        beautify_try(solver, l, false);
    }
  }
}

/*******************************************************************\

Function: counterexample_beautification_greedyt::get_max_width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned counterexample_beautification_greedyt::get_max_width(
  const namespacet &ns,
  const typet &type)
{
  // array or struct?

  if(type.id()==ID_array)
  {
    return get_max_width(ns, type.subtype());
  }
  else if(type.id()==ID_struct)
  {
    const irept::subt &components=type.find(ID_components).get_sub();
    unsigned max_width=0;

    forall_irep(it, components)
    {
      const typet &subtype=
        static_cast<const typet &>(it->find(ID_type));
      max_width=std::max(max_width, get_max_width(ns, subtype));
    }

    return max_width;
  }
  else if(type.id()==ID_symbol)
  {
    const symbolt &s=ns.lookup(type.get(ID_identifier));
    return get_max_width(ns, s.type);
  }
  else if(type.id()==ID_pointer)
  {
  }
  else
  {
    boolbv_widtht boolbv_width(ns);
    return boolbv_width(type);
  }

  return 0;
}

/*******************************************************************\

Function: counterexample_beautification_greedyt::beautify_values

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_greedyt::beautify_values(
  solvert &solver,
  bv_cbmct &bv_cbmc,
  symex_target_equationt &equation,      
  const namespacet &ns)
{
  // get symbols we care about
  minimization_symbolst minimization_symbols;

  get_minimization_symbols(bv_cbmc, equation, failed, minimization_symbols);

  // get max width
  unsigned max_width=0;

  for(minimization_symbolst::const_iterator it=minimization_symbols.begin();
      it!=minimization_symbols.end(); it++)
    max_width=std::max(max_width, get_max_width(ns, it->type()));

  for(unsigned i=0; i<max_width; i++)
    for(minimization_symbolst::const_iterator it=minimization_symbols.begin();
        it!=minimization_symbols.end(); it++)
      minimize(solver, bv_cbmc, ns, *it, it->type(), 0, i);
}

/*******************************************************************\

Function: counterexample_beautification_greedyt::beautify_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct guard_structt
{
  guard_structt(literalt _literal, unsigned _count):
    literal(_literal), count(_count) { }

  literalt literal;
  unsigned count;
};

struct guard_comp:
  public std::binary_function<guard_structt, guard_structt, bool>
{
  bool operator()(const guard_structt &x,
                  const guard_structt &y) const
  { return x.count<y.count; }
};

void counterexample_beautification_greedyt::beautify_guards(
  solvert &solver,
  bv_cbmct &bv_cbmc,
  symex_target_equationt &equation,
  const namespacet &ns)
{
  // lock the failed assertion
  {
    bvt clause;
    clause.push_back(solver.lnot(failed->cond_literal));
    solver.lcnf(clause);
  }

  // compute weights
  typedef std::map<literalt, unsigned> guard_countt;
  guard_countt guard_count;

  for(symex_target_equationt::SSA_stepst::const_iterator
      it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end(); it++)
  {
    if(it->is_assignment() &&
       it->assignment_type!=symex_targett::HIDDEN)
    {
      if(!it->guard_literal.is_constant())
        guard_count[it->guard_literal]++;
    }

    // reached failed assertion?
    if(it==failed)
      break;
  }

  // put it in a vector to sort it
  typedef std::vector<guard_structt> guard_vectort;
  guard_vectort guard_vector;

  guard_vector.reserve(guard_count.size());

  for(guard_countt::const_iterator
      it=guard_count.begin();
      it!=guard_count.end();
      it++)
    guard_vector.push_back(guard_structt(it->first, it->second));

  // sort it
  std::sort(guard_vector.begin(), guard_vector.end(), guard_comp());

  // minimize, starting with the largest one

  for(guard_vectort::const_reverse_iterator
      it=guard_vector.rbegin();
      it!=static_cast<const guard_vectort &>(guard_vector).rend();
      it++)
    beautify_try(solver, it->literal, false);
}

/*******************************************************************\

Function: counterexample_beautification_greedyt::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_greedyt::operator()(
  solvert &solver,
  bv_cbmct &bv_cbmc,
  symex_target_equationt &equation,
  const namespacet &ns)
{
  // find failed claim

  failed=get_failed_claim(bv_cbmc, equation);

  bv_cbmc.status("Beautifying Counterexample (Guards)");
  beautify_guards(solver, bv_cbmc, equation, ns);

  bv_cbmc.status("Beautifying Counterexample (Values)");
  beautify_values(solver, bv_cbmc, equation, ns);
}

/*******************************************************************\

Function: counterexample_beautification_greedyt::save_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_greedyt::save_assignment(propt &prop)
{
  assignment.resize(prop.no_variables());

  for(unsigned i=1; i<prop.no_variables(); i++)
    assignment[i]=prop.l_get(literalt(i, false)).is_true();
}

/*******************************************************************\

Function: counterexample_beautification_greedyt::restore_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void counterexample_beautification_greedyt::restore_assignment(propt &prop)
{
  assert(assignment.size()==prop.no_variables());

  for(unsigned i=1; i<prop.no_variables(); i++)
    prop.set_assignment(literalt(i, false), assignment[i]);
}
