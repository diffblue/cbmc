/*******************************************************************\

Module: Squolem Backend

Author: CM Wintersteiger

\*******************************************************************/

/// \file
/// Squolem Backend

#include "qbf_squolem.h"

qbf_squolemt::qbf_squolemt():
  early_decision(false)
{
}

qbf_squolemt::~qbf_squolemt()
{
  squolem.reset();
}

tvt qbf_squolemt::l_get(literalt a) const
{
  UNREACHABLE;
}

const std::string qbf_squolemt::solver_text()
{
  return "Squolem";
}

propt::resultt qbf_squolemt::prop_solve()
{
  {
    std::string msg=
      "Squolem: "+
      std::to_string(no_variables())+" variables, "+
      std::to_string(no_clauses())+" clauses";
    messaget::status() << msg << messaget::eom;
  }

  if(early_decision)
    return P_UNSATISFIABLE;

//  squolem.options.set_showStatus(true);
  squolem.options.set_freeOnExit(true);
//  squolem.options.set_useExpansion(true);
//  squolem.options.set_predictOnLiteralBound(true);
  squolem.options.set_debugFilename("debug.qdimacs");
  squolem.options.set_saveDebugFile(true);

  squolem.endOfOriginals();
  bool result=squolem.decide();

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

void qbf_squolemt::lcnf(const bvt &bv)
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

  if(!squolem.addClause(buffer))
    early_decision=true;
}

void qbf_squolemt::add_quantifier(const quantifiert &quantifier)
{
  squolem.quantifyVariableInner(
    quantifier.var_no,
    quantifier.type==quantifiert::UNIVERSAL);

  qdimacs_cnft::add_quantifier(quantifier); // necessary?
}

void qbf_squolemt::set_no_variables(unsigned no)
{
  squolem.setLastVariable(no+1);
  cnft::set_no_variables(no);
}

void qbf_squolemt::set_quantifier(
  const quantifiert::typet type,
  const literalt l)
{
  qdimacs_cnft::set_quantifier(type, l);
  squolem.requantifyVariable(l.var_no(), type==quantifiert::UNIVERSAL);
}
