/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>

#include "interval_domain.h"

/*******************************************************************\

Function: interval_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::output(
  std::ostream &out,
  const ai_baset &ai,
  const namespacet &ns) const
{
  if(bottom)
  {
    out << "BOTTOM\n";
    return;
  }

  for(const auto &interval : int_map)
  {
    if(interval.second.is_top()) continue;
    if(interval.second.lower_set)
      out << interval.second.lower << " <= ";
    out << interval.first;
    if(interval.second.upper_set)
      out << " <= " << interval.second.upper;
    out << "\n";
  }

  for(const auto &interval : float_map)
  {
    if(interval.second.is_top()) continue;
    if(interval.second.lower_set)
      out << interval.second.lower << " <= ";
    out << interval.first;
    if(interval.second.upper_set)
      out << " <= " << interval.second.upper;
    out << "\n";
  }
}

/*******************************************************************\

Function: interval_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::transform(
  locationt from,
  locationt to,
  ai_baset &ai,
  const namespacet &ns)
{
  const goto_programt::instructiont &instruction=*from;
  switch(instruction.type)
  {
  case DECL:
    havoc_rec(to_code_decl(instruction.code).symbol());
    break;

  case DEAD:
    havoc_rec(to_code_dead(instruction.code).symbol());
    break;

  case ASSIGN:
    assign(to_code_assign(instruction.code));
    break;

  case GOTO:
    {
      locationt next=from;
      next++;
      if(next==to)
        assume(not_exprt(instruction.guard), ns);
      else
        assume(instruction.guard, ns);
    }
    break;

  case ASSUME:
    assume(instruction.guard, ns);
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code_function_call=
        to_code_function_call(instruction.code);
      if(code_function_call.lhs().is_not_nil())
        havoc_rec(code_function_call.lhs());
    }
    break;

  default:;
  }
}

/*******************************************************************\

Function: interval_domaint::join

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool interval_domaint::join(
  const interval_domaint &b)
{
  if(b.bottom) return false;
  if(bottom) { *this=b; return true; }

  bool result=false;

  for(int_mapt::iterator it=int_map.begin();
      it!=int_map.end(); ) // no it++
  {
    const int_mapt::const_iterator b_it=b.int_map.begin();
    if(b_it==b.int_map.end())
    {
      it=int_map.erase(it);
      result=true;
    }
    else
    {
      integer_intervalt previous=it->second;
      it->second.join(b_it->second);
      if(it->second!=previous) result=true;

      it++;
    }
  }

  for(float_mapt::iterator it=float_map.begin();
      it!=float_map.end(); ) // no it++
  {
    const float_mapt::const_iterator b_it=b.float_map.begin();
    if(b_it==b.float_map.end())
    {
      it=float_map.erase(it);
      result=true;
    }
    else
    {
      ieee_float_intervalt previous=it->second;
      it->second.join(b_it->second);
      if(it->second!=previous) result=true;

      it++;
    }
  }

  return result;
}

/*******************************************************************\

Function: interval_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::assign(const code_assignt &code_assign)
{
  havoc_rec(code_assign.lhs());
  assume_rec(code_assign.lhs(), ID_equal, code_assign.rhs());
}

/*******************************************************************\

Function: interval_domaint::havoc_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::havoc_rec(const exprt &lhs)
{
  if(lhs.id()==ID_if)
  {
    havoc_rec(to_if_expr(lhs).true_case());
    havoc_rec(to_if_expr(lhs).false_case());
  }
  else if(lhs.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(lhs).get_identifier();

    if(is_int(lhs.type()))
      int_map.erase(identifier);
    else if(is_float(lhs.type()))
      float_map.erase(identifier);
  }
  else if(lhs.id()==ID_typecast)
  {
    havoc_rec(to_typecast_expr(lhs).op());
  }
}

/*******************************************************************\

Function: interval_domaint::assume_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::assume_rec(
  const exprt &lhs, irep_idt id, const exprt &rhs)
{
  if(lhs.id()==ID_typecast)
    return assume_rec(to_typecast_expr(lhs).op(), id, rhs);

  if(rhs.id()==ID_typecast)
    return assume_rec(lhs, id, to_typecast_expr(rhs).op());

  if(id==ID_equal)
  {
    assume_rec(lhs, ID_ge, rhs);
    assume_rec(lhs, ID_le, rhs);
    return;
  }

  if(id==ID_notequal)
    return; // won't do split

  if(id==ID_ge)
    return assume_rec(rhs, ID_le, lhs);

  if(id==ID_gt)
    return assume_rec(rhs, ID_lt, lhs);

  // we now have lhs <  rhs or
  //             lhs <= rhs

  assert(id==ID_lt || id==ID_le);

  #ifdef DEBUG
  std::cout << "assume_rec: "
            << from_expr(lhs) << " " << id << " "
            << from_expr(rhs) << "\n";
  #endif

  if(lhs.id()==ID_symbol && rhs.id()==ID_constant)
  {
    irep_idt lhs_identifier=to_symbol_expr(lhs).get_identifier();

    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      mp_integer tmp;
      to_integer(rhs, tmp);
      if(id==ID_lt) --tmp;
      integer_intervalt &ii=int_map[lhs_identifier];
      ii.make_le_than(tmp);
      if(ii.is_bottom()) make_bottom();
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_floatt tmp(to_constant_expr(rhs));
      if(id==ID_lt) tmp.decrement();
      ieee_float_intervalt &fi=float_map[lhs_identifier];
      fi.make_le_than(tmp);
      if(fi.is_bottom()) make_bottom();
    }
  }
  else if(lhs.id()==ID_constant && rhs.id()==ID_symbol)
  {
    irep_idt rhs_identifier=to_symbol_expr(rhs).get_identifier();

    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      mp_integer tmp;
      to_integer(lhs, tmp);
      if(id==ID_lt) ++tmp;
      integer_intervalt &ii=int_map[rhs_identifier];
      ii.make_ge_than(tmp);
      if(ii.is_bottom()) make_bottom();
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_floatt tmp(to_constant_expr(lhs));
      if(id==ID_lt) tmp.increment();
      ieee_float_intervalt &fi=float_map[rhs_identifier];
      fi.make_ge_than(tmp);
      if(fi.is_bottom()) make_bottom();
    }
  }
  else if(lhs.id()==ID_symbol && rhs.id()==ID_symbol)
  {
    irep_idt lhs_identifier=to_symbol_expr(lhs).get_identifier();
    irep_idt rhs_identifier=to_symbol_expr(rhs).get_identifier();

    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      integer_intervalt &lhs_i=int_map[lhs_identifier];
      integer_intervalt &rhs_i=int_map[rhs_identifier];
      lhs_i.meet(rhs_i);
      rhs_i=lhs_i;
      if(rhs_i.is_bottom()) make_bottom();
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_float_intervalt &lhs_i=float_map[lhs_identifier];
      ieee_float_intervalt &rhs_i=float_map[rhs_identifier];
      lhs_i.meet(rhs_i);
      rhs_i=lhs_i;
      if(rhs_i.is_bottom()) make_bottom();
    }
  }
}

/*******************************************************************\

Function: interval_domaint::assume_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::assume(
  const exprt &cond,
  const namespacet &ns)
{
  assume_rec(simplify_expr(cond, ns), false);
}

/*******************************************************************\

Function: interval_domaint::assume_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void interval_domaint::assume_rec(
  const exprt &cond,
  bool negation)
{
  if(cond.id()==ID_lt || cond.id()==ID_le ||
     cond.id()==ID_gt || cond.id()==ID_ge ||
     cond.id()==ID_equal || cond.id()==ID_notequal)
  {
    assert(cond.operands().size()==2);

    if(negation) // !x<y  ---> x>=y
    {
      if(cond.id()==ID_lt)
        assume_rec(cond.op0(), ID_ge, cond.op1());
      else if(cond.id()==ID_le)
        assume_rec(cond.op0(), ID_gt, cond.op1());
      else if(cond.id()==ID_gt)
        assume_rec(cond.op0(), ID_le, cond.op1());
      else if(cond.id()==ID_ge)
        assume_rec(cond.op0(), ID_lt, cond.op1());
      else if(cond.id()==ID_equal)
        assume_rec(cond.op0(), ID_notequal, cond.op1());
      else if(cond.id()==ID_notequal)
        assume_rec(cond.op0(), ID_equal, cond.op1());
    }
    else
      assume_rec(cond.op0(), cond.id(), cond.op1());
  }
  else if(cond.id()==ID_not)
  {
    assume_rec(to_not_expr(cond).op(), !negation);
  }
  else if(cond.id()==ID_and)
  {
    if(!negation)
      forall_operands(it, cond)
        assume_rec(*it, false);
  }
  else if(cond.id()==ID_or)
  {
    if(negation)
      forall_operands(it, cond)
        assume_rec(*it, true);
  }
}

/*******************************************************************\

Function: interval_domaint::make_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt interval_domaint::make_expression(const symbol_exprt &src) const
{
  if(is_int(src.type()))
  {
    int_mapt::const_iterator i_it=int_map.find(src.get_identifier());
    if(i_it==int_map.end()) return true_exprt();
    const integer_intervalt &interval=i_it->second;
    if(interval.is_top()) return true_exprt();
    if(interval.is_bottom()) return false_exprt();

    exprt::operandst conjuncts;

    if(interval.upper_set)
    {
      exprt tmp=from_integer(interval.upper, src.type());
      conjuncts.push_back(binary_relation_exprt(src, ID_le, tmp));
    }

    if(interval.lower_set)
    {
      exprt tmp=from_integer(interval.lower, src.type());
      conjuncts.push_back(binary_relation_exprt(tmp, ID_le, src));
    }

    return conjunction(conjuncts);
  }
  else if(is_float(src.type()))
  {
    float_mapt::const_iterator i_it=float_map.find(src.get_identifier());
    if(i_it==float_map.end()) return true_exprt();
    const ieee_float_intervalt &interval=i_it->second;
    if(interval.is_top()) return true_exprt();
    if(interval.is_bottom()) return false_exprt();

    exprt::operandst conjuncts;

    if(interval.upper_set)
    {
      exprt tmp=interval.upper.to_expr();
      conjuncts.push_back(binary_relation_exprt(src, ID_le, tmp));
    }

    if(interval.lower_set)
    {
      exprt tmp=interval.lower.to_expr();
      conjuncts.push_back(binary_relation_exprt(tmp, ID_le, src));
    }

    return conjunction(conjuncts);
  }
  else
    return true_exprt();
}

/*******************************************************************\

Function: interval_domaint::domain_simplify

  Inputs: The expression to simplify.

 Outputs: A simplified version of the expression.

 Purpose: Uses the domain to simplify a given expression using context-specific information.

\*******************************************************************/

exprt interval_domaint::domain_simplify(
  const exprt &condition,
  const namespacet &ns,
  const bool lhs) const
{
  if(lhs)
  {
    // For now do not simplify the left hand side of assignments
    return condition;
  }

  interval_domaint d(*this);

  // merge intervals to properly handle conjunction
  if(condition.id()==ID_and)
  {
    interval_domaint a;
    a.make_top();
    a.assume(condition, ns);

#ifdef DEBUG
    a.output(std::cout, interval_analysis, ns);
    d.output(std::cout, interval_analysis, ns);
#endif

    if(!a.join(d))
    {
      exprt e;
      e.make_true();
      return e;
    }
  }
  else if(condition.id()==ID_symbol)
  {
    // TODO: we have to handle symbol expression
  }
  else
  {
    d.assume(not_exprt(condition), ns);
    if(d.is_bottom())
    {
      exprt e;
      e.make_true();
      return e;
    }
  }

  return condition;
}
