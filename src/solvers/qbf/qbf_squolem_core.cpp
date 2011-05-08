/*******************************************************************\

Module: Squolem Backend (with proofs)

Author: CM Wintersteiger

\*******************************************************************/

#include <algorithm>

#include <util/i2string.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>

#include <ansi-c/c_types.h> // uint type for indices

#include "qbf_squolem_core.h"

/*******************************************************************\

Function: qbf_squolem_coret::qbf_squolem_coret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_squolem_coret::qbf_squolem_coret() : squolem(NULL)
{
  setup();
}

/*******************************************************************\

Function: qbf_squolem_coret::setup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: qbf_squolem_coret::reset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolem_coret::reset(void)
{
  squolem->reset();
  delete(squolem);
  squolem=NULL;
  setup();
}

/*******************************************************************\

Function: qbf_squolem_coret::~qbf_squolem_coret

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_squolem_coret::~qbf_squolem_coret()
{
  squolem->reset();
  delete(squolem);
  squolem=NULL;
}

/*******************************************************************\

Function: qbf_squolem_coret::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt qbf_squolem_coret::l_get(literalt a) const
{
  if(a.is_true())
    return tvt(tvt::TV_TRUE);
  else if(a.is_false())
    return tvt(tvt::TV_FALSE);
  else if(squolem->modelIsTrue(a.var_no()))
    return tvt(tvt::TV_TRUE);
  else if(squolem->modelIsFalse(a.var_no()) ||
          squolem->modelIsDontCare(a.var_no()))
    return tvt(tvt::TV_FALSE);
  else
    return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: qbf_squolem_coret::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string qbf_squolem_coret::solver_text()
{
  return "Squolem (Certifying)";
}

/*******************************************************************\

Function: qbf_squolem_coret::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt qbf_squolem_coret::prop_solve()
{
  {
    std::string msg=
      "Squolem: "+
      i2string(no_variables())+" variables, "+
      i2string(no_clauses())+" clauses";
    messaget::status(msg);
  }

  squolem->endOfOriginals();
  bool result = squolem->decide();

  if(result)
  {
    messaget::status("Squolem: VALID");
    return P_SATISFIABLE;
  }
  else
  {
    messaget::status("Squolem: INVALID");
    return P_UNSATISFIABLE;
  }

  return P_ERROR;
}

/*******************************************************************\

Function: qbf_squolem_coret::is_in_core

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool qbf_squolem_coret::is_in_core(literalt l) const
{
  return squolem->inCore(l.var_no());
}

/*******************************************************************\

Function: qbf_squolem_coret::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: qbf_squolem_coret::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolem_coret::lcnf(const bvt &bv)
{
  if(early_decision) return; // we don't need no more...

  bvt new_bv;

  if(process_clause(bv, new_bv))
    return;

  if(new_bv.size()==0)
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
  while (i<new_bv.size());

  if(!squolem->addClause(buffer))
    early_decision=true;
}

/*******************************************************************\

Function: qbf_squolem_coret::add_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolem_coret::add_quantifier(const quantifiert &quantifier)
{
  squolem->quantifyVariableInner(quantifier.var_no,
                                quantifier.type==quantifiert::UNIVERSAL);

  qdimacs_cnft::add_quantifier(quantifier); // necessary?
}

/*******************************************************************\

Function: qbf_squolem_coret::set_no_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolem_coret::set_no_variables(unsigned no)
{
  squolem->setLastVariable(no+1);
  cnft::set_no_variables(no);
}

/*******************************************************************\

Function: qbf_squolem_coret::set_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolem_coret::set_quantifier(
  const quantifiert::typet type,
  const literalt l)
{
  qdimacs_cnft::set_quantifier(type, l);
  squolem->requantifyVariable(l.var_no(), type==quantifiert::UNIVERSAL);
}

/*******************************************************************\

Function: qbf_squolem_coret::set_debug_filename

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolem_coret::set_debug_filename(const std::string &str)
{
  squolem->options.set_debugFilename(str.c_str());
}

/*******************************************************************\

Function: qbf_squolem_coret::write_qdimacs_cnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolem_coret::write_qdimacs_cnf(std::ostream &out)
{
  squolem->saveQCNF(out);
}

/*******************************************************************\

Function: qbf_squolem_coret::f_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt qbf_squolem_coret::f_get(literalt l)
{
  if(squolem->isUniversal(l.var_no()))
  {
    assert(l.var_no()!=0);
    variable_mapt::const_iterator it=variable_map.find(l.var_no());

    if(it==variable_map.end())
      throw "Variable map error";

    const exprt &sym=it->second.first;
    unsigned index=it->second.second;

    exprt extract_expr("extractbit", typet("bool"));
    extract_expr.copy_to_operands(sym);
    typet uint_type("unsignedbv");
    uint_type.set("width", 32);
    extract_expr.copy_to_operands(from_integer(index, uint_type));

    if(l.sign()) extract_expr.negate();

    return extract_expr;
  }

  function_cachet::const_iterator it=function_cache.find(l.var_no());
  if(it!=function_cache.end())
  {
    #if 0
    std::cout << "CACHE HIT for " << l.dimacs() << std::endl;
    #endif

    if(l.sign())
      return not_exprt(it->second);
    else
      return it->second;
  }
  else
  {
    WitnessStack *wsp = squolem->getModelFunction(Literal(l.dimacs()));
    exprt res;

    if(wsp==NULL || wsp->size()==0)
    {
//      res=exprt("nondet_bool", typet("bool"));
      res=false_exprt(); // just set it to zero
    }
    else if(wsp->pSize<=wsp->nSize)
      res=f_get_cnf(wsp);
    else
      res=f_get_dnf(wsp);

    function_cache[l.var_no()] = res;

    if(l.sign())
      return not_exprt(res);
    else
      return res;
  }
}

/*******************************************************************\

Function: qbf_squolem_coret::f_get_cnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt qbf_squolem_coret::f_get_cnf(WitnessStack *wsp)
{
  Clause *p=wsp->negWits;

  if(!p) return exprt("true", typet("bool"));

  exprt::operandst operands;

  while(p!=NULL)
  {
    exprt clause=or_exprt();

    for(unsigned i=0; i<p->size; i++)
    {
      const Literal &lit=p->literals[i];
      exprt subf = f_get(literalt(var(lit), isPositive(lit))); // negated!
      if(find(clause.operands().begin(), clause.operands().end(), subf)==
         clause.operands().end())
        clause.move_to_operands(subf);
    }

    if(clause.operands().size()==0)
      clause=false_exprt();
    else if(clause.operands().size()==1)
    {
      const exprt tmp=clause.op0();
      clause=tmp;
    }

    #if 0
    std::cout << "CLAUSE: " << clause << std::endl;
    #endif

    operands.push_back(clause);

    p=p->next;
  }

  return and_exprt(operands);
}

/*******************************************************************\

Function: qbf_squolem_coret::f_get_dnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const exprt qbf_squolem_coret::f_get_dnf(WitnessStack *wsp)
{
  Clause *p=wsp->posWits;

  if(!p) return exprt("false", typet("bool"));

  exprt::operandst operands;

  while(p!=NULL)
  {
    exprt cube=and_exprt();

    for(unsigned i=0; i<p->size; i++)
    {
      const Literal &lit=p->literals[i];
      exprt subf = f_get(literalt(var(lit), !isPositive(lit)));
      if(find(cube.operands().begin(), cube.operands().end(), subf)==
         cube.operands().end())
        cube.move_to_operands(subf);

      simplify_extractbits(cube);
    }

    if(cube.operands().size()==0)
      cube=true_exprt();
    else if(cube.operands().size()==1)
    {
      const exprt tmp=cube.op0();
      cube=tmp;
    }

    #if 0
    std::cout << "CUBE: " << cube << std::endl;
    #endif

    operands.push_back(cube);

    p=p->next;
  }

  return or_exprt(operands);
}
