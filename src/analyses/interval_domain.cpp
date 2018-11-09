/*******************************************************************\

Module: Interval Domain

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Interval Domain

#include "interval_domain.h"

#ifdef DEBUG
#include <iostream>
#include <langapi/language_util.h>
#endif

#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/arith_tools.h>

void interval_domaint::output(
  std::ostream &out,
  const ai_baset &,
  const namespacet &) const
{
  if(bottom)
  {
    out << "BOTTOM\n";
    return;
  }

  for(const auto &interval : int_map)
  {
    if(interval.second.is_top())
      continue;
    if(interval.second.lower_set)
      out << interval.second.lower << " <= ";
    out << interval.first;
    if(interval.second.upper_set)
      out << " <= " << interval.second.upper;
    out << "\n";
  }

  for(const auto &interval : float_map)
  {
    if(interval.second.is_top())
      continue;
    if(interval.second.lower_set)
      out << interval.second.lower << " <= ";
    out << interval.first;
    if(interval.second.upper_set)
      out << " <= " << interval.second.upper;
    out << "\n";
  }
}

void interval_domaint::transform(
  const irep_idt &,
  locationt from,
  const irep_idt &,
  locationt to,
  ai_baset &,
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
      // Comparing iterators is safe as the target must be within the same list
      // of instructions because this is a GOTO.
      locationt next=from;
      next++;
      if(from->get_target() != next) // If equal then a skip
      {
        if(next == to)
          assume(not_exprt(instruction.guard), ns);
        else
          assume(instruction.guard, ns);
      }
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

  default:
    {
    }
  }
}

/// Sets *this to the mathematical join between the two domains. This can be
/// thought of as an abstract version of union; *this is increased so that it
/// contains all of the values that are represented by b as well as its original
/// intervals. The result is an overapproximation, for example:
/// "[0,1]".join("[3,4]") --> "[0,4]" includes 2 which isn't in [0,1] or [3,4].
///
///          Join is used in several places, the most significant being
///          merge, which uses it to bring together two different paths
///          of analysis.
/// \par parameters: The interval domain, b, to join to this domain.
/// \return True if the join increases the set represented by *this, False if
///   there is no change.
bool interval_domaint::join(
  const interval_domaint &b)
{
  if(b.bottom)
    return false;
  if(bottom)
  {
    *this=b;
    return true;
  }

  bool result=false;

  for(int_mapt::iterator it=int_map.begin();
      it!=int_map.end(); ) // no it++
  {
    // search for the variable that needs to be merged
    // containers have different size and variable order
    const int_mapt::const_iterator b_it=b.int_map.find(it->first);
    if(b_it==b.int_map.end())
    {
      it=int_map.erase(it);
      result=true;
    }
    else
    {
      integer_intervalt previous=it->second;
      it->second.join(b_it->second);
      if(it->second!=previous)
        result=true;

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
      if(it->second!=previous)
        result=true;

      it++;
    }
  }

  return result;
}

void interval_domaint::assign(const code_assignt &code_assign)
{
  havoc_rec(code_assign.lhs());
  assume_rec(code_assign.lhs(), ID_equal, code_assign.rhs());
}

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
      mp_integer tmp = numeric_cast_v<mp_integer>(rhs);
      if(id==ID_lt)
        --tmp;
      integer_intervalt &ii=int_map[lhs_identifier];
      ii.make_le_than(tmp);
      if(ii.is_bottom())
        make_bottom();
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_floatt tmp(to_constant_expr(rhs));
      if(id==ID_lt)
        tmp.decrement();
      ieee_float_intervalt &fi=float_map[lhs_identifier];
      fi.make_le_than(tmp);
      if(fi.is_bottom())
        make_bottom();
    }
  }
  else if(lhs.id()==ID_constant && rhs.id()==ID_symbol)
  {
    irep_idt rhs_identifier=to_symbol_expr(rhs).get_identifier();

    if(is_int(lhs.type()) && is_int(rhs.type()))
    {
      mp_integer tmp = numeric_cast_v<mp_integer>(lhs);
      if(id==ID_lt)
        ++tmp;
      integer_intervalt &ii=int_map[rhs_identifier];
      ii.make_ge_than(tmp);
      if(ii.is_bottom())
        make_bottom();
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_floatt tmp(to_constant_expr(lhs));
      if(id==ID_lt)
        tmp.increment();
      ieee_float_intervalt &fi=float_map[rhs_identifier];
      fi.make_ge_than(tmp);
      if(fi.is_bottom())
        make_bottom();
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
      if(rhs_i.is_bottom())
        make_bottom();
    }
    else if(is_float(lhs.type()) && is_float(rhs.type()))
    {
      ieee_float_intervalt &lhs_i=float_map[lhs_identifier];
      ieee_float_intervalt &rhs_i=float_map[rhs_identifier];
      lhs_i.meet(rhs_i);
      rhs_i=lhs_i;
      if(rhs_i.is_bottom())
        make_bottom();
    }
  }
}

void interval_domaint::assume(
  const exprt &cond,
  const namespacet &ns)
{
  assume_rec(simplify_expr(cond, ns), false);
}

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

exprt interval_domaint::make_expression(const symbol_exprt &src) const
{
  if(is_int(src.type()))
  {
    int_mapt::const_iterator i_it=int_map.find(src.get_identifier());
    if(i_it==int_map.end())
      return true_exprt();

    const integer_intervalt &interval=i_it->second;
    if(interval.is_top())
      return true_exprt();
    if(interval.is_bottom())
      return false_exprt();

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
    if(i_it==float_map.end())
      return true_exprt();

    const ieee_float_intervalt &interval=i_it->second;
    if(interval.is_top())
      return true_exprt();
    if(interval.is_bottom())
      return false_exprt();

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

/// Uses the abstract state to simplify a given expression using context-
/// specific information.
/// \par parameters: The expression to simplify.
/// \return A simplified version of the expression.
/*
 * This implementation is aimed at reducing assertions to true, particularly
 * range checks for arrays and other bounds checks.
 *
 * Rather than work with the various kinds of exprt directly, we use assume,
 * join and is_bottom.  It is sufficient for the use case and avoids duplicating
 * functionality that is in assume anyway.
 *
 * As some expressions (1<=a && a<=2) can be represented exactly as intervals
 * and some can't (a<1 || a>2), the way these operations are used varies
 * depending on the structure of the expression to try to give the best results.
 * For example negating a disjunction makes it easier for assume to handle.
 */

bool interval_domaint::ai_simplify(
  exprt &condition,
  const namespacet &ns) const
{
  bool unchanged=true;
  interval_domaint d(*this);

  // merge intervals to properly handle conjunction
  if(condition.id()==ID_and)              // May be directly representable
  {
    interval_domaint a;
    a.make_top();                         // a is everything
    a.assume(condition, ns);              // Restrict a to an over-approximation
                                          //  of when condition is true
    if(!a.join(d))                        // If d (this) is included in a...
    {                                     // Then the condition is always true
      unchanged=condition.is_true();
      condition.make_true();
    }
  }
  else if(condition.id()==ID_symbol)
  {
    // TODO: we have to handle symbol expression
  }
  else                                    // Less likely to be representable
  {
    d.assume(not_exprt(condition), ns);   // Restrict to when condition is false
    if(d.is_bottom())                     // If there there are none...
    {                                     // Then the condition is always true
      unchanged=condition.is_true();
      condition.make_true();
    }
  }

  return unchanged;
}
