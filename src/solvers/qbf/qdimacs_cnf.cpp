/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>
#include <cassert>

#include "qdimacs_cnf.h"

/*******************************************************************\

Function: qdimacs_cnft::write_qdimacs_cnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qdimacs_cnft::write_qdimacs_cnf(std::ostream &out)
{
  write_problem_line(out);
  write_prefix(out);
  write_clauses(out);
}

/*******************************************************************\

Function: qdimacs_cnft::write_prefix

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qdimacs_cnft::write_prefix(std::ostream &out) const
{
  std::vector<bool> quantified;

  quantified.resize(no_variables(), false);

  for(quantifierst::const_iterator
      it=quantifiers.begin();
      it!=quantifiers.end();
      it++)
  {
    const quantifiert &quantifier=*it;

    assert(quantifier.var_no<no_variables());
    // double quantification?
    assert(!quantified[quantifier.var_no]);
    quantified[quantifier.var_no]=true;

    switch(quantifier.type)
    {
    case quantifiert::UNIVERSAL:
      out << "a";
      break;

    case quantifiert::EXISTENTIAL:
      out << "e";
      break;

    default:
      assert(false);
    }

    out << " " << quantifier.var_no << " 0" << std::endl;
  }

  // variables that are not quantified
  // will be quantified existentially in the innermost scope

  for(unsigned i=1; i<no_variables(); i++)
    if(!quantified[i])
      out << "e " << i << " 0" << std::endl;
}

/*******************************************************************\

Function: operator==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator==(const qdimacs_cnft &a, const qdimacs_cnft &b)
{
  return a.quantifiers==b.quantifiers &&
         a.clauses==b.clauses;
}

/*******************************************************************\

Function: qdimacs_cnft::set_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qdimacs_cnft::set_quantifier(
  const quantifiert::typet type,
  const literalt l)
{
  for(quantifierst::iterator it=quantifiers.begin();
      it!=quantifiers.end();
      it++)
    if(it->var_no==l.var_no())
    {
      it->type=type;
      return;
    }

  // variable not found - let's add a new quantifier.
  add_quantifier(type, l);
}

/*******************************************************************\

Function: qdimacs_cnft::copy_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qdimacs_cnft::copy_to(qdimacs_cnft &cnf) const
{
  cnf.set_no_variables(_no_variables);

  for(quantifierst::const_iterator
      it=quantifiers.begin();
      it!=quantifiers.end();
      it++)
    cnf.add_quantifier(*it);

  for(clausest::const_iterator
      it=clauses.begin();
      it!=clauses.end();
      it++)
    cnf.lcnf(*it);
}

/*******************************************************************\

Function: qdimacs_cnft::hash

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

size_t qdimacs_cnft::hash() const
{
  size_t result=0;

  for(quantifierst::const_iterator it=quantifiers.begin();
      it!=quantifiers.end();
      it++)
    result=((result<<1)^it->hash())-result;

  return result^cnf_clause_listt::hash();
}

/*******************************************************************\

Function: qdimacs_cnft::is_quantified

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool qdimacs_cnft::is_quantified(const literalt l) const
{
  for(quantifierst::const_iterator it=quantifiers.begin();
      it!=quantifiers.end();
      it++)
    if(it->var_no==l.var_no())
      return true;

  return false;
}

/*******************************************************************\

Function: qdimacs_cnft::find_quantifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool qdimacs_cnft::find_quantifier(const literalt l, quantifiert &q) const
{
  for(quantifierst::const_iterator it=quantifiers.begin();
      it!=quantifiers.end();
      it++)
    if(it->var_no==l.var_no())
    {
      q=*it;
      return true;
    }

  return false;
}
