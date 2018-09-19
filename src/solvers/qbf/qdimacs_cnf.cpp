/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "qdimacs_cnf.h"

#include <iostream>

#include <util/invariant.h>

void qdimacs_cnft::write_qdimacs_cnf(std::ostream &out)
{
  write_problem_line(out);
  write_prefix(out);
  write_clauses(out);
}

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

    INVARIANT_WITH_DIAGNOSTICS(
      quantifier.var_no < no_variables(),
      "unknown variable: ",
      std::to_string(quantifier.var_no));
    // double quantification?
    INVARIANT(!quantified[quantifier.var_no], "no double quantification");
    quantified[quantifier.var_no]=true;

    switch(quantifier.type)
    {
    case quantifiert::typet::UNIVERSAL:
      out << "a";
      break;

    case quantifiert::typet::EXISTENTIAL:
      out << "e";
      break;

    default:
      UNREACHABLE;
    }

    out << " " << quantifier.var_no << " 0\n";
  }

  // variables that are not quantified
  // will be quantified existentially in the innermost scope

  for(std::size_t i=1; i<no_variables(); i++)
    if(!quantified[i])
      out << "e " << i << " 0\n";
}

bool qdimacs_cnft::operator==(const qdimacs_cnft &other) const
{
  return quantifiers==other.quantifiers && clauses==other.clauses;
}

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

size_t qdimacs_cnft::hash() const
{
  size_t result=0;

  for(quantifierst::const_iterator it=quantifiers.begin();
      it!=quantifiers.end();
      it++)
    result=((result<<1)^it->hash())-result;

  return result^cnf_clause_listt::hash();
}

bool qdimacs_cnft::is_quantified(const literalt l) const
{
  for(quantifierst::const_iterator it=quantifiers.begin();
      it!=quantifiers.end();
      it++)
    if(it->var_no==l.var_no())
      return true;

  return false;
}

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
