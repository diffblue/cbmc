/*******************************************************************\

Module: Squolem Backend

Author: CM Wintersteiger

\*******************************************************************/

#include <util/i2string.h>

#include "qbf_squolem.h"

/*******************************************************************\

Function: qbf_squolemt::qbf_squolemt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_squolemt::qbf_squolemt() : early_decision(false)
{
}

/*******************************************************************\

Function: qbf_squolemt::~qbf_squolemt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

qbf_squolemt::~qbf_squolemt()
{
  squolem.reset();
}

/*******************************************************************\

Function: qbf_squolemt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt qbf_squolemt::l_get(literalt a) const
{
  assert(false);
}

/*******************************************************************\

Function: qbf_squolemt::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string qbf_squolemt::solver_text()
{
  return "Squolem";
}

/*******************************************************************\

Function: qbf_squolemt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt qbf_squolemt::prop_solve()
{
  {
    std::string msg=
      "Squolem: "+
      i2string(no_variables())+" variables, "+
      i2string(no_clauses())+" clauses";
    messaget::status(msg);
  }

  if(early_decision) return P_UNSATISFIABLE;

//  squolem.options.set_showStatus(true);
  squolem.options.set_freeOnExit(true);
//  squolem.options.set_useExpansion(true);
//  squolem.options.set_predictOnLiteralBound(true);
  squolem.options.set_debugFilename("debug.qdimacs");
  squolem.options.set_saveDebugFile(true);

  squolem.endOfOriginals();
  bool result = squolem.decide();

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

Function: qbf_squolemt::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolemt::lcnf(const bvt &bv)
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

  if(!squolem.addClause(buffer))
    early_decision=true;
}

/*******************************************************************\

Function: qbf_squolemt::add_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolemt::add_quantifier(const quantifiert &quantifier)
{
  squolem.quantifyVariableInner(quantifier.var_no,
                                quantifier.type==quantifiert::UNIVERSAL);

  qdimacs_cnft::add_quantifier(quantifier); // necessary?
}

/*******************************************************************\

Function: qbf_squolemt::set_no_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolemt::set_no_variables(unsigned no)
{
  squolem.setLastVariable(no+1);
  cnft::set_no_variables(no);
}

/*******************************************************************\

Function: qbf_squolemt::set_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qbf_squolemt::set_quantifier(
  const quantifiert::typet type,
  const literalt l)
{
  qdimacs_cnft::set_quantifier(type, l);
  squolem.requantifyVariable(l.var_no(), type==quantifiert::UNIVERSAL);
}
