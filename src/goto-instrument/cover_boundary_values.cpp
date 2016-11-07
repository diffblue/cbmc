/*******************************************************************\

Module: Coverage Instrumentation for Boundary Values

Author: Youcheng Sun

Date: Oct 2016

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <util/prefix.h>
#include <util/i2string.h>
#include <util/expr_util.h>

#include "cover.h"

/*******************************************************************\

Function: non_ordered_predicate_expansion

  Inputs:

 Outputs:

 Purpose: expand a non-ordered predicate: <=, !=, >=

\*******************************************************************/

std::set<exprt> non_ordered_predicate_expansion(const exprt &src)
{
  std::set<exprt> result;
  // the expansion of "<=" is "<" and "=="
  if(src.id()==ID_le)
  {
    exprt e1(ID_lt);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);

    exprt e2(ID_equal);
    e2.type().id(src.type().id());
    e2.operands().push_back(src.op0());
    e2.operands().push_back(src.op1());
    result.insert(e2);
  }
  if(src.id()==ID_ge)
  {
    exprt e1(ID_gt);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);

    exprt e2(ID_equal);
    e2.type().id(src.type().id());
    e2.operands().push_back(src.op0());
    e2.operands().push_back(src.op1());
    result.insert(e2);
  }
  if(src.id()==ID_notequal)
  {

    if(from_expr(src.op0())=="TRUE"
       or from_expr(src.op0())=="FALSE"
       or from_expr(src.op1())=="TRUE"
       or from_expr(src.op1())=="FALSE")
    {
      return result;
    }
    exprt e1(ID_gt);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);

    exprt e2(ID_lt);
    e2.type().id(src.type().id());
    e2.operands().push_back(src.op0());
    e2.operands().push_back(src.op1());
    result.insert(e2);
  }

  return result;

}

/*******************************************************************\

Function: ordered_negation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<exprt> ordered_negation(const exprt &src)
{
  std::set<exprt> result;
  // the negation of "==" is "<" and ">"
  if(src.id()==ID_equal)
  {
    exprt e1(ID_le);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);

    exprt e2(ID_ge);
    e2.type().id(src.type().id());
    e2.operands().push_back(src.op0());
    e2.operands().push_back(src.op1());
    result.insert(e2);
  }
  // the negation of "<" is "==" and ">"
  if(src.id()==ID_lt)
  {
    exprt e1(ID_equal);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);

    exprt e2(ID_gt);
    e2.type().id(src.type().id());
    e2.operands().push_back(src.op0());
    e2.operands().push_back(src.op1());
    result.insert(e2);
  }
  // the negation of "<=" is ">"
  if(src.id()==ID_le)
  {
    exprt e1(ID_gt);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);
  }
  // the negation of ">=" is "<"
  if(src.id()==ID_ge)
  {
    exprt e1(ID_lt);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);
  }
  // the negation of ">" is "==" and "<"
  if(src.id()==ID_gt)
  {
    exprt e1(ID_equal);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);

    exprt e2(ID_lt);
    e2.type().id(src.type().id());
    e2.operands().push_back(src.op0());
    e2.operands().push_back(src.op1());
    result.insert(e2);
  }
  // the negation of "!=" is "=="
  if(src.id()==ID_notequal)
  {
    exprt e1(ID_equal);
    e1.type().id(src.type().id());
    e1.operands().push_back(src.op0());
    e1.operands().push_back(src.op1());
    result.insert(e1);
  }

  return result;

}

/*******************************************************************\

Function: non_ordered_expr_expansion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<exprt> non_ordered_expr_expansion(const exprt &src)
{
  std::set<exprt> result;

  std::set<exprt> s1, s2;

  if(src.id()!=ID_not) s1.insert(src);
  else
  {
    exprt no=src.op0();
    if(is_arithmetic_predicate(no))
    {
      auto res=ordered_negation(no);
      for(auto &e: res) s1.insert(e);
    }
    else result.insert(src);
  }

  // expand negations and non-ordered predicates
  while(true)
  {
    bool changed=false;
    for(auto &x: s1)
    {
      std::vector<exprt> operands;
      collect_operands(x, operands);
      for(int i=0; i<operands.size(); i++)
      {
        std::set<exprt> res;
        if(operands[i].id()==ID_not)
        {
          exprt no=operands[i].op0();
          if(is_arithmetic_predicate(no))
          {
            res=ordered_negation(no);
            if(res.size()>0) changed=true;
          }
        }
        else
        {
          if(operands[i].id()==ID_le
             or operands[i].id()==ID_ge
             or operands[i].id()==ID_notequal)
          {
            res=non_ordered_predicate_expansion(operands[i]);
            if(res.size()>0) changed=true;
          }
        }
        std::set<exprt> co=replacement_and_conjunction(res, operands, i);
        s2.insert(co.begin(), co.end());
        if(res.size()>0) break;
      }
      if(not changed) s2.insert(x);
    }
    if(not changed) break;
    s1=s2;
    s2.clear();
  }

  return s1;

}

/*******************************************************************\

Function: decision_expansion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<exprt> decision_expansion(const exprt &dec)
{
  std::set<exprt> ctrl;
  // dec itself may be a non-ordered predicate
  exprt d(dec);
  if(d.id()==ID_not) d=d.op0();
  if(is_arithmetic_predicate(d))
  {
    auto res=non_ordered_predicate_expansion(d);
    if(not res.empty())
      ctrl.insert(res.begin(), res.end());
    else ctrl.insert(d);
    d.make_not();
    res=non_ordered_predicate_expansion(d);
    if(not res.empty())
      ctrl.insert(res.begin(), res.end());
    else ctrl.insert(d);
  }
  return ctrl;
}

/*******************************************************************\

Function: is_arithmetic_predicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_arithmetic_predicate(const exprt &src)
{
  if(src.id()==ID_lt
     or src.id()==ID_le
     or src.id()==ID_equal
     or src.id()==ID_ge
     or src.id()==ID_gt
     or src.id()==ID_notequal)
    return true;

  return false;
}
