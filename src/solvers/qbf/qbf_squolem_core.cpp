/*******************************************************************\

Module: Squolem Backend (with proofs)

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Squolem Backend (with proofs)

#include "qbf_squolem_core.h"

#include <algorithm>

#include <util/std_expr.h>
#include <util/arith_tools.h>

#include <util/c_types.h> // uint type for indices

qbf_squolem_coret::qbf_squolem_coret() : squolem(NULL)
{
  setup();
}

void qbf_squolem_coret::setup(void)
{
  quantifiers.clear();
  clauses.clear();
  early_decision=false;
  variable_map.clear();
  squolem=new Squolem2();

//  squolem->options.set_extractCoreVariables(true);
//  squolem->options.set_saveCertificate(true);
  squolem->options.set_keepModelFunctions(true);
  squolem->options.set_keepResolutionProof(false);
  squolem->options.set_freeOnExit(true);
//  squolem->options.set_useExpansion(true);
  squolem->options.set_debugFilename("debug.qdimacs");
  squolem->options.set_saveDebugFile(true);
  squolem->options.set_compressModel(true);
//  squolem->options.set_showStatus(true);
//  squolem->options.set_predictOnLiteralBound(true);
}

void qbf_squolem_coret::reset(void)
{
  squolem->reset();
  delete(squolem);
  squolem=NULL;
  setup();
}

qbf_squolem_coret::~qbf_squolem_coret()
{
  squolem->reset();
  delete(squolem);
  squolem=NULL;
}

tvt qbf_squolem_coret::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(tvt::tv_enumt::TV_TRUE);
  else if(a.is_false())
    return tvt(tvt::tv_enumt::TV_FALSE);
  else if(squolem->modelIsTrue(a.var_no()))
    return tvt(tvt::tv_enumt::TV_TRUE);
  else if(squolem->modelIsFalse(a.var_no()) ||
          squolem->modelIsDontCare(a.var_no()))
    return tvt(tvt::tv_enumt::TV_FALSE);
  else
    return tvt(tvt::tv_enumt::TV_UNKNOWN);
}

const std::string qbf_squolem_coret::solver_text()
{
  return "Squolem (Certifying)";
}

propt::resultt qbf_squolem_coret::prop_solve()
{
  {
    std::string msg=
      "Squolem: "+
      std::to_string(no_variables())+" variables, "+
      std::to_string(no_clauses())+" clauses";
    messaget::status() << msg << messaget::eom;
  }

  squolem->endOfOriginals();
  bool result=squolem->decide();

  if(result)
  {
    messaget::status() << "Squolem: VALID" << messaget::eom;
    return P_SATISFIABLE;
  }
  else
  {
    messaget::status() << "Squolem: INVALID" << messaget::eom;
    return P_UNSATISFIABLE;
  }

  return P_ERROR;
}

bool qbf_squolem_coret::is_in_core(literalt l) const
{
  return squolem->inCore(l.var_no());
}

qbf_squolem_coret::modeltypet qbf_squolem_coret::m_get(literalt a) const
{
  if(squolem->modelIsTrue(a.var_no()))
    return M_TRUE;
  else if(squolem->modelIsFalse(a.var_no()))
    return M_FALSE;
  else if(squolem->modelIsComplex(a.var_no()))
    return M_COMPLEX;
  else
    return M_DONTCARE;
}

void qbf_squolem_coret::lcnf(const bvt &bv)
{
  if(early_decision)
    return; // we don't need no more...

  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  if(new_bv.empty())
  {
    early_decision=true;
    return;
  }

  std::vector<Literal> buffer(new_bv.size());
  unsigned long i=0;
  do
  {
    buffer[i]=new_bv[i].dimacs();
    i++;
  }
  while(i<new_bv.size());

  if(!squolem->addClause(buffer))
    early_decision=true;
}

void qbf_squolem_coret::add_quantifier(const quantifiert &quantifier)
{
  squolem->quantifyVariableInner(
    quantifier.var_no,
    quantifier.type==quantifiert::UNIVERSAL);

  qdimacs_cnft::add_quantifier(quantifier); // necessary?
}

void qbf_squolem_coret::set_no_variables(unsigned no)
{
  squolem->setLastVariable(no+1);
  cnft::set_no_variables(no);
}

void qbf_squolem_coret::set_quantifier(
  const quantifiert::typet type,
  const literalt l)
{
  qdimacs_cnft::set_quantifier(type, l);
  squolem->requantifyVariable(l.var_no(), type==quantifiert::UNIVERSAL);
}

void qbf_squolem_coret::set_debug_filename(const std::string &str)
{
  squolem->options.set_debugFilename(str.c_str());
}

void qbf_squolem_coret::write_qdimacs_cnf(std::ostream &out)
{
  squolem->saveQCNF(out);
}

const exprt qbf_squolem_coret::f_get(literalt l)
{
  if(squolem->isUniversal(l.var_no()))
  {
    INVARIANT_WITH_DIAGNOSTICS(
      l.var_no() != 0, "unknown variable: ", std::to_string(l.var_no()));
    variable_mapt::const_iterator it=variable_map.find(l.var_no());

    INVARIANT(
      it != variable_map.end(), "variable not found in the variable map");

    const exprt &sym=it->second.first;
    unsigned index=it->second.second;

    extractbit_exprt extract_expr(sym, from_integer(index, integer_typet()));

    if(l.sign())
      extract_expr.negate();

    return extract_expr;
  }

  function_cachet::const_iterator it=function_cache.find(l.var_no());
  if(it!=function_cache.end())
  {
    #if 0
    std::cout << "CACHE HIT for " << l.dimacs() << '\n';
    #endif

    if(l.sign())
      return not_exprt(it->second);
    else
      return it->second;
  }
  else
  {
    WitnessStack *wsp=squolem->getModelFunction(Literal(l.dimacs()));
    exprt res;

    if(wsp==NULL || wsp->empty())
    {
//      res=exprt(ID_nondet_bool, typet(ID_bool));
      res=false_exprt(); // just set it to zero
    }
    else if(wsp->pSize<=wsp->nSize)
      res=f_get_cnf(wsp);
    else
      res=f_get_dnf(wsp);

    function_cache[l.var_no()]=res;

    if(l.sign())
      return not_exprt(res);
    else
      return res;
  }
}

const exprt qbf_squolem_coret::f_get_cnf(WitnessStack *wsp)
{
  Clause *p=wsp->negWits;

  if(!p)
    return exprt(ID_true, typet(ID_bool));

  exprt::operandst operands;

  while(p!=NULL)
  {
    or_exprt clause;

    for(unsigned i=0; i<p->size; i++)
    {
      const Literal &lit=p->literals[i];
      exprt subf=f_get(literalt(var(lit), isPositive(lit))); // negated!
      if(find(clause.operands().begin(), clause.operands().end(), subf)==
         clause.operands().end())
        clause.add_to_operands(std::move(subf));
    }

    if(clause.operands().empty())
      clause=false_exprt();
    else if(clause.operands().size()==1)
    {
      const exprt tmp=clause.op0();
      clause=tmp;
    }

    #if 0
    std::cout << "CLAUSE: " << clause << '\n';
    #endif

    operands.push_back(clause);

    p=p->next;
  }

  return and_exprt(operands);
}

const exprt qbf_squolem_coret::f_get_dnf(WitnessStack *wsp)
{
  Clause *p=wsp->posWits;

  if(!p)
    return exprt(ID_false, typet(ID_bool));

  exprt::operandst operands;

  while(p!=NULL)
  {
    and_exprt cube;

    for(unsigned i=0; i<p->size; i++)
    {
      const Literal &lit=p->literals[i];
      exprt subf=f_get(literalt(var(lit), !isPositive(lit)));
      if(find(cube.operands().begin(), cube.operands().end(), subf)==
         cube.operands().end())
        cube.add_to_operands(std::move(subf));

      simplify_extractbits(cube);
    }

    if(cube.operands().empty())
      cube=true_exprt();
    else if(cube.operands().size()==1)
    {
      const exprt tmp=cube.op0();
      cube=tmp;
    }

    #if 0
    std::cout << "CUBE: " << cube << '\n';
    #endif

    operands.push_back(cube);

    p=p->next;
  }

  return or_exprt(operands);
}
