/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <util/prefix.h>
#include <util/i2string.h>
#include <util/expr_util.h>

#include "cover.h"

/*******************************************************************\

Function: as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const char *as_string(coverage_criteriont c)
{
  switch(c)
  {
  case coverage_criteriont::LOCATION: return "location";
  case coverage_criteriont::BRANCH: return "branch";
  case coverage_criteriont::DECISION: return "decision";
  case coverage_criteriont::CONDITION: return "condition";
  case coverage_criteriont::PATH: return "path";
  case coverage_criteriont::MCDC: return "MC/DC";
  case coverage_criteriont::ASSERTION: return "assertion";
  case coverage_criteriont::COVER: return "cover instructions";
  default: return "";
  }
}

/*******************************************************************\

Function: is_condition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool is_condition(const exprt &src)
{
  if(src.type().id()!=ID_bool) return false;

  // conditions are 'atomic predicates'
  if(src.id()==ID_and || src.id()==ID_or ||
     src.id()==ID_not || src.id()==ID_implies)
    return false;

  return true;
}

/*******************************************************************\

Function: collect_conditions_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void collect_conditions_rec(
  const exprt &src,
  std::set<exprt> &dest)
{
  if(src.id()==ID_address_of)
  {
    return;
  }

  for(const auto & op : src.operands())
    collect_conditions_rec(op, dest);

  if(is_condition(src) && !src.is_constant())
    dest.insert(src);
}

/*******************************************************************\

Function: collect_conditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::set<exprt> collect_conditions(const exprt &src)
{
  std::set<exprt> result;
  collect_conditions_rec(src, result);
  return result;
}

/*******************************************************************\

Function: collect_conditions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::set<exprt> collect_conditions(
  const goto_programt::const_targett t)
{
  switch(t->type)
  {
  case GOTO:
  case ASSERT:
    return collect_conditions(t->guard);

  case ASSIGN:
  case FUNCTION_CALL:
    return collect_conditions(t->code);

  default: {}
  }

  return std::set<exprt>();
}

/*******************************************************************\

Function: collect_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void collect_operands(
  const exprt &src,
  std::vector<exprt> &dest)
{
  for(const exprt &op : src.operands())
  {
    if(op.id()==src.id())
      collect_operands(op, dest);
    else
      dest.push_back(op);
  }
}

/*******************************************************************\

Function: non_ordered_predicate_expansion

  Inputs:

 Outputs:

 Purpose: A non-ordered predicate contains <=, !=, >=

\*******************************************************************/

static std::set<exprt> non_ordered_predicate_expansion(
  const exprt &src)
{
  std::set<exprt> result;
  // the expansion of "<=" is "<" and "=="
  if(src.id()==ID_le)
  {
    exprt e1(src);
    e1.id(ID_lt);
    result.insert(e1);

    exprt e2(src);
    e1.id(ID_equal);
    result.insert(e2);
  }
  // the expansion of ">=" is ">" and "=="
  else if(src.id()==ID_ge)
  {
    exprt e1(src);
    e1.id(ID_gt);
    result.insert(e1);

    exprt e2(src);
    e1.id(ID_equal);
    result.insert(e2);
  }
  else if(src.id()==ID_notequal)
  {
    if(src.op0().type().id()==ID_c_bool
       || src.op1().type().id()==ID_c_bool)
    {
      return result;
    }
    // the expansion of "==" is ">" and "<"
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

static std::set<exprt> ordered_negation(const exprt &src)
{
  std::set<exprt> result;
  // the negation of "==" is "<" and ">"
  if(src.id()==ID_equal)
  {
    exprt e1(src);
    e1.id(ID_lt);
    result.insert(e1);

    exprt e2(src);
    e2.id(ID_gt);
    result.insert(e2);
  }
  // the negation of "<" is "==" and ">"
  else if(src.id()==ID_lt)
  {
    exprt e1(src);
    e1.id(ID_equal);
    result.insert(e1);

    exprt e2(src);
    e2.id(ID_gt);
    result.insert(e2);
  }
  // the negation of "<=" is ">"
  else if(src.id()==ID_le)
  {
    exprt e1(src);
    e1.id(ID_gt);
    result.insert(e1);
  }
  // the negation of ">=" is "<"
  else if(src.id()==ID_ge)
  {
    exprt e1(src);
    e1.id(ID_lt);
    result.insert(e1);
  }
  // the negation of ">" is "==" and "<"
  else if(src.id()==ID_gt)
  {
    exprt e1(src);
    e1.id(ID_equal);
    result.insert(e1);

    exprt e2(src);
    e2.id(ID_lt);
    result.insert(e2);
  }
  // the negation of "!=" is "=="
  else if(src.id()==ID_notequal)
  {
    exprt e1(src);
    e1.id(ID_equal);
    result.insert(e1);
  }

  return result;
}

/*******************************************************************\

Function: is_arithmetic_predicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool is_arithmetic_predicate(const exprt &src)
{
  return (src.id()==ID_lt
          || src.id()==ID_le
          || src.id()==ID_equal
          || src.id()==ID_ge
          || src.id()==ID_gt
          || src.id()==ID_notequal);
}

/*******************************************************************\

Function: replacement_and_conjunction

  Inputs:

 Outputs:

 Purpose: To replace the i-th expr of ''operands'' with each
          expr inside ''replacement_exprs''.

\*******************************************************************/

static std::set<exprt> replacement_and_conjunction(
  const std::set<exprt> &replacement_exprs,
  const std::vector<exprt> &operands,
  const std::size_t i)
{
  std::set<exprt> result;
  for(auto &y : replacement_exprs)
  {
    assert(operands.size()>i);
    std::vector<exprt> others(operands);
    others[i]=y;
    exprt c=conjunction(others);
    result.insert(c);
  }
  return result;
}

/*******************************************************************\

Function: non_ordered_expr_expansion

  Inputs:

 Outputs:

 Purpose: To expand all non ordered predicates within an expr

\*******************************************************************/

static std::set<exprt> non_ordered_expr_expansion(const exprt &src)
{
  if(src.id()==ID_not && is_arithmetic_predicate(src.op0()))
  {
    return ordered_negation(src.op0());
  }

  std::set<exprt> result;
  std::vector<exprt> operands;;
  collect_operands(src, operands);
  // expand negations and non-ordered predicates
  for(std::size_t i=0; i<operands.size(); ++i)
  {
    // an 'op' can be expanded if 1) it is a 'not' or 2) it
    // is a predicate with '<=', '>=' or '!='
    std::set<exprt> expanded_op;
    if(operands[i].id()==ID_not)
    {
      const exprt &no=operands[i].op0();
      if(is_arithmetic_predicate(no))
      {
        expanded_op=ordered_negation(no);
      }
    }
    else
    {
      if(operands[i].id()==ID_le
         || operands[i].id()==ID_ge
         || operands[i].id()==ID_notequal)
      {
        expanded_op=non_ordered_predicate_expansion(operands[i]);
      }
    }
    if(expanded_op.empty()) continue;
    auto re=replacement_and_conjunction(expanded_op, operands, i);
    for(auto &x : re)
    {
      auto rec_result=non_ordered_expr_expansion(x);
      result.insert(rec_result.begin(), rec_result.end());
    }
    // The loop can terminate as long as one 'op' has been expanded,
    // since the recursive call will handle other expansions.
    return result;
  }
  return {src};
}

/*******************************************************************\

Function: decision_expansion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::set<exprt> decision_expansion(const exprt &dec)
{
  std::set<exprt> ctrl;
  // dec itself may be a non-ordered predicate
  exprt d(dec);
  if(d.id()==ID_not) d=d.op0();
  if(is_arithmetic_predicate(d))
  {
    auto res=non_ordered_expr_expansion(d);
    ctrl.insert(res.begin(), res.end());
    d.make_not();
    res=non_ordered_expr_expansion(d);
    ctrl.insert(res.begin(), res.end());
  }
  return ctrl;
}

/*******************************************************************\

Function: collect_mcdc_controlling_rec

  Inputs:

 Outputs:

 Purpose: To recursively collect controlling exprs for
          for mcdc coverage.

\*******************************************************************/

static void collect_mcdc_controlling_rec(
  const exprt &src,
  const std::vector<exprt> &conditions,
  std::set<exprt> &result)
{
  // src is conjunction (ID_and) or disjunction (ID_or)
  if(src.id()==ID_and ||
     src.id()==ID_or)
  {
    std::vector<exprt> operands;
    collect_operands(src, operands);

    if(operands.size()==1)
    {
      exprt e=*operands.begin();
      collect_mcdc_controlling_rec(e, conditions, result);
    }
    else if(!operands.empty())
    {
      for(std::size_t i=0; i<operands.size(); i++)
      {
        const exprt op=operands[i];

        if(is_condition(op))
        {
          if(src.id()==ID_or)
          {
            std::vector<exprt> others1, others2;
            if(!conditions.empty())
            {
              others1.push_back(conjunction(conditions));
              others2.push_back(conjunction(conditions));
            }

            for(std::size_t j=0; j<operands.size(); j++)
            {
              others1.push_back(not_exprt(operands[j]));
              if(i!=j)
                others2.push_back(not_exprt(operands[j]));
              else
                others2.push_back((operands[j]));
            }

            result.insert(conjunction(others1));
            result.insert(conjunction(others2));
            continue;
          }

          std::vector<exprt> o=operands;

          // 'o[i]' needs to be true and false
          std::vector<exprt> new_conditions=conditions;
          new_conditions.push_back(conjunction(o));
          result.insert(conjunction(new_conditions));

          o[i].make_not();
          new_conditions.back()=conjunction(o);
          result.insert(conjunction(new_conditions));
        }
        else
        {
          std::vector<exprt> others;
          others.reserve(operands.size()-1);

          for(std::size_t j=0; j<operands.size(); j++)
            if(i!=j)
            {
              if(src.id()==ID_or)
                others.push_back(not_exprt(operands[j]));
              else
                others.push_back(operands[j]);
            }

          exprt c=conjunction(others);
          std::vector<exprt> new_conditions=conditions;
          new_conditions.push_back(c);

          collect_mcdc_controlling_rec(op, new_conditions, result);
        }
      }
    }
  }
  else if(src.id()==ID_not)
  {
    exprt e=to_not_expr(src).op();
    if(!is_condition(e))
      collect_mcdc_controlling_rec(e, conditions, result);
    else
    {
      // to store a copy of ''src''
      std::vector<exprt> new_conditions1=conditions;
      new_conditions1.push_back(src);
      result.insert(conjunction(new_conditions1));

      // to store a copy of its negation, i.e., ''e''
      std::vector<exprt> new_conditions2=conditions;
      new_conditions2.push_back(e);
      result.insert(conjunction(new_conditions2));
    }
  }
  else
  {
    /**
     * It may happen that ''is_condition(src)'' is valid,
     * but we ignore this case here as it can be handled
     * by the routine decision/condition detection.
     **/
  }
}

/*******************************************************************\

Function: collect_mcdc_controlling

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::set<exprt> collect_mcdc_controlling(
  const std::set<exprt> &decisions)
{
  std::set<exprt> result;

  for(const auto &d : decisions)
  {
    collect_mcdc_controlling_rec(d, { }, result);
  }

  return result;
}


/*******************************************************************\

Function: collect_mcdc_controlling_nested

  Inputs:

 Outputs:

 Purpose: This nested method iteratively applies
          ''collect_mcdc_controlling'' to every non-atomic expr
          within a decision

\*******************************************************************/

static std::set<exprt> collect_mcdc_controlling_nested(
  const std::set<exprt> &decisions)
{
  // To obtain the 1st-level controlling conditions
  std::set<exprt> controlling = collect_mcdc_controlling(decisions);

  std::set<exprt> result;
  // For each controlling condition, to check if it contains
  // non-atomic exprs
  for(auto &src : controlling)
  {
    std::set<exprt> s1, s2;
    /**
     * The final controlling conditions resulted from ''src''
     * will be stored in ''s1''; ''s2'' is used to hold the
     * temporary expansion.
     **/
    s1.insert(src);

    // dual-loop structure to eliminate complex
    // non-atomic-conditional terms
    bool changed=true;
    while(changed)
    {
      changed=false;
      // the 2nd loop
      for(auto &x : s1)
      {
        // if ''x'' is atomic conditional term, there
        // is no expansion
        if(is_condition(x))
        {
          s2.insert(x);
          continue;
        }
        // otherwise, we apply the ''nested'' method to
        // each of its operands
        std::vector<exprt> operands;
        collect_operands(x, operands);

        for(std::size_t i=0; i<operands.size(); i++)
        {
          std::set<exprt> res;
          /**
           * To expand an operand if it is not atomic,
           * and label the ''changed'' flag; the resulted
           * expansion of such an operand is stored in ''res''.
           **/
          if(operands[i].id()==ID_not)
          {
            exprt no=operands[i].op0();
            if(!is_condition(no))
            {
              changed=true;
              std::set<exprt> ctrl_no;
              ctrl_no.insert(no);
              res=collect_mcdc_controlling(ctrl_no);
            }
          }
          else if(!is_condition(operands[i]))
          {
            changed=true;
            std::set<exprt> ctrl;
            ctrl.insert(operands[i]);
            res=collect_mcdc_controlling(ctrl);
          }

          // To replace a non-atomic expr with its expansion
          std::set<exprt> co=
            replacement_and_conjunction(res, operands, i);
          s2.insert(co.begin(), co.end());
          if(!res.empty()) break;
        }
        // if there is no change x.r.t current operands of ''x'',
        // i.e., they are all atomic, we reserve ''x''
        if(!changed) s2.insert(x);
      }
      // update ''s1'' and check if change happens
      s1.swap(s2);
      s2.clear();
      if(!changed) {break;}
    }

    // The expansions of each ''src'' should be added into
    // the ''result''
    result.insert(s1.begin(), s1.end());
  }

  return result;
}

/*******************************************************************\

Function: sign_of_expr

  Inputs: E should be the pre-processed output by
          ''collect_mcdc_controlling_nested''

 Outputs: +1 : not negated
          -1 : negated

 Purpose: The sign of expr ''e'' within the super-expr ''E''

\*******************************************************************/

static std::set<signed> sign_of_expr(const exprt &e, const exprt &E)
{
  std::set<signed> signs;

  // At fist, we pre-screen the case such that ''E''
  // is an atomic condition
  if(is_condition(E))
  {
    if(e==E)
      signs.insert(+1);
    return signs;
  }

  // or, ''E'' is the negation of ''e''?
  if(E.id()==ID_not)
  {
    if(e==E.op0())
    {
      signs.insert(-1);
      return signs;
    }
  }

  /**
   * In the general case, we analyze each operand of ''E''.
   **/
  std::vector<exprt> ops;
  collect_operands(E, ops);
  for(auto &x : ops)
  {
    exprt y(x);
    if(y==e) signs.insert(+1);
    else if(y.id()==ID_not)
    {
      y.make_not();
      if(y==e) signs.insert(-1);
      if(!is_condition(y))
      {
        std::set<signed> re=sign_of_expr(e, y);
        signs.insert(re.begin(), re.end());
      }
    }
    else if(!is_condition(y))
    {
      std::set<signed> re=sign_of_expr(e, y);
      signs.insert(re.begin(), re.end());
    }
  }

  return signs;
}

/*******************************************************************\

Function: remove_repetition

  Inputs:

 Outputs:

 Purpose: After the ''collect_mcdc_controlling_nested'', there
          can be the recurrence of the same expr in the resulted
          set of exprs, and this method will remove the
          repetitive ones.

\*******************************************************************/

static void remove_repetition(std::set<exprt> &exprs)
{
  // to obtain the set of atomic conditions
  std::set<exprt> conditions;
  for(auto &x : exprs)
  {
    std::set<exprt> new_conditions = collect_conditions(x);
    conditions.insert(new_conditions.begin(), new_conditions.end());
  }
  // exprt that contains multiple (inconsistent) signs should
  // be removed
  std::set<exprt> new_exprs;
  for(auto &x : exprs)
  {
    bool kept=true;
    for(auto &c : conditions)
    {
      std::set<signed> signs=sign_of_expr(c, x);
      if(signs.size()>1)
      {
        kept=false;
        break;
      }
    }
    if(kept) new_exprs.insert(x);
  }
  exprs=new_exprs;
  new_exprs.clear();

  for(auto &x : exprs)
  {
    bool red=false;
    /**
     * To check if ''x'' is identical with some
     * expr in ''new_exprs''. Two exprs ''x''
     * and ''y'' are identical iff they have the
     * same sign for every atomic condition ''c''.
     **/
    for(auto &y : new_exprs)
    {
      bool iden = true;
      for(auto &c : conditions)
      {
        std::set<signed> signs1=sign_of_expr(c, x);
        std::set<signed> signs2=sign_of_expr(c, y);
        std::size_t s1=signs1.size(), s2=signs2.size();
        // it is easy to check non-equivalence;
        if(s1!=s2)
        {
          iden=false;
          break;
        }
        else
        {
          if(s1==0 && s2==0) continue;
          // it is easy to check non-equivalence
          if(*(signs1.begin())!=*(signs2.begin()))
          {
            iden=false;
            break;
          }
        }
      }
      /**
       * If ''x'' is found identical w.r.t some
       * expr in ''new_conditions, we label it
       * and break.
       **/
      if(iden)
      {
        red=true;
        break;
      }
    }
    // an expr is added into ''new_exprs''
    // if it is not found repetitive
    if(!red) new_exprs.insert(x);
  }

  // update the original ''exprs''
  exprs.swap(new_exprs);
}

/*******************************************************************\

Function: eval_expr

  Inputs:

 Outputs:

 Purpose: To evaluate the value of expr ''src'', according to
          the atomic expr values

\*******************************************************************/

static bool eval_expr(
  const std::map<exprt, signed> &atomic_exprs,
  const exprt &src)
{
  std::vector<exprt> operands;
  collect_operands(src, operands);
  // src is AND
  if(src.id()==ID_and)
  {
    for(auto &x : operands)
      if(!eval_expr(atomic_exprs, x))
        return false;
    return true;
  }
  // src is OR
  else if(src.id()==ID_or)
  {
    std::size_t fcount=0;

    for(auto &x : operands)
      if(!eval_expr(atomic_exprs, x))
        fcount++;

    if(fcount<operands.size())
      return true;
    else
      return false;
  }
  // src is NOT
  else if(src.id()==ID_not)
  {
    exprt no_op(src);
    no_op.make_not();
    return !eval_expr(atomic_exprs, no_op);
  }
  else // if(is_condition(src))
  {
    // ''src'' should be guaranteed to be consistent
    // with ''atomic_exprs''
    if(atomic_exprs.find(src)->second==+1)
      return true;
    else // if(atomic_exprs.find(src)->second==-1)
      return false;
  }
}

/*******************************************************************\

Function: values_of_atomic_exprs

  Inputs:

 Outputs:

 Purpose: To obtain values of atomic exprs within the super expr

\*******************************************************************/

static std::map<exprt, signed> values_of_atomic_exprs(
  const exprt &e,
  const std::set<exprt> &conditions)
{
  std::map<exprt, signed> atomic_exprs;
  for(auto &c : conditions)
  {
    std::set<signed> signs=sign_of_expr(c, e);
    if(signs.empty())
    {
      // ''c'' is not contained in ''e''
      atomic_exprs.insert(std::pair<exprt, signed>(c, 0));
      continue;
    }
    // we do not consider inconsistent expr ''e''
    if(signs.size()!=1) continue;

    atomic_exprs.insert(
      std::pair<exprt, signed>(c, *signs.begin()));
  }
  return atomic_exprs;
}

/*******************************************************************\

Function: is_mcdc_pair

  Inputs:

 Outputs:

 Purpose: To check if the two input controlling exprs are mcdc
          pairs regarding an atomic expr ''c''. A mcdc pair of
          (e1, e2) regarding ''c'' means that ''e1'' and ''e2''
          result in different ''decision'' values, and this is
          caused by the different choice of ''c'' value.

\*******************************************************************/

static bool is_mcdc_pair(
  const exprt &e1,
  const exprt &e2,
  const exprt &c,
  const std::set<exprt> &conditions,
  const exprt &decision)
{
  // An controlling expr cannot be mcdc pair of itself
  if(e1==e2) return false;

  // To obtain values of each atomic condition within ''e1''
  // and ''e2''
  std::map<exprt, signed> atomic_exprs_e1=
    values_of_atomic_exprs(e1, conditions);
  std::map<exprt, signed> atomic_exprs_e2=
    values_of_atomic_exprs(e2, conditions);

  // the sign of ''c'' inside ''e1'' and ''e2''
  signed cs1=atomic_exprs_e1.find(c)->second;
  signed cs2=atomic_exprs_e2.find(c)->second;
  // a mcdc pair should both contain ''c'', i.e., sign=+1 or -1
  if(cs1==0 || cs2==0)
    return false;

  // A mcdc pair regarding an atomic expr ''c''
  // should have different values of ''c''
  if(cs1==cs2)
    return false;

  // A mcdc pair should result in different ''decision''
  if(eval_expr(atomic_exprs_e1, decision)==
     eval_expr(atomic_exprs_e2, decision))
    return false;

  /**
   *  A mcdc pair of controlling exprs regarding ''c''
   *  can have different values for only one atomic
   *  expr, i.e., ''c''. Otherwise, they are not
   *  a mcdc pair.
   **/
  int diff_count=0;
  auto e1_it=atomic_exprs_e1.begin();
  auto e2_it=atomic_exprs_e2.begin();
  while(e1_it!=atomic_exprs_e1.end())
  {
    if(e1_it->second!=e2_it->second)
    diff_count++;
    if(diff_count>1) break;
    e1_it++;
    e2_it++;
  }

  if(diff_count==1) return true;
  else
    return false;
}

/*******************************************************************\

Function: has_mcdc_pair

  Inputs:

 Outputs:

 Purpose: To check if we can find the mcdc pair of the
          input ''expr_set'' regarding the atomic expr ''c''

\*******************************************************************/

static bool has_mcdc_pair(
  const exprt &c,
  const std::set<exprt> &expr_set,
  const std::set<exprt> &conditions,
  const exprt &decision)
{
  for(auto y1 : expr_set)
  {
    for(auto y2 : expr_set)
    {
      if(is_mcdc_pair(y1, y2, c, conditions, decision))
      {
        return true;
      }
    }
  }
  return false;
}

/*******************************************************************\

Function: minimize_mcdc_controlling

  Inputs: The input ''controlling'' should have been processed by
          ''collect_mcdc_controlling_nested''
                  and
          ''remove_repetition''

 Outputs:

 Purpose: This method minimizes the controlling conditions for
          mcdc coverage. The minimum is in a sense that by deleting
          any controlling condition in the set, the mcdc coverage
          for the decision will be not complete.

\*******************************************************************/

static void minimize_mcdc_controlling(
  std::set<exprt> &controlling,
  const exprt &decision)
{
  // to obtain the set of atomic conditions
  std::set<exprt> conditions;
  for(auto &x : controlling)
  {
    std::set<exprt> new_conditions = collect_conditions(x);
    conditions.insert(new_conditions.begin(), new_conditions.end());
  }

  bool ctrl_update=true;
  while(ctrl_update)
  {
    ctrl_update=false;
    std::set<exprt> new_controlling;
    /**
     * Iteratively, we test that after removing an item ''x''
     * from the ''controlling'', can a complete mcdc coverage
     * over ''decision'' still be reserved?
     *
     * If yes, we update ''controlling'' with the
     * ''new_controlling'' without ''x''; otherwise, we should
     * keep ''x'' within ''controlling''.
     *
     * If in the end all elements ''x'' in ''controlling'' are
     * reserved, this means that current ''controlling'' set is
     * minimum and the ''while'' loop should be breaked.
     *
     * Note:  implementaion here for the above procedure is
     *        not (meant to be) optimal.
     **/
    for(auto &x : controlling)
    {
      // To create a new ''controlling'' set without ''x''
      new_controlling.clear();
      for(auto &y : controlling)
        if(y!=x) new_controlling.insert(y);

      bool removing_x=true;
      // For each atomic expr condition ''c'', to check if its is
      // covered by at least a mcdc pair.
      for(auto &c : conditions)
      {
        bool cOK=
          has_mcdc_pair(c, new_controlling, conditions, decision);
        /**
         *  If there is no mcdc pair for an atomic condition ''c'',
         *  then ''x'' should not be removed from the original
         *  ''controlling'' set
         **/
        if(!cOK)
        {
          removing_x=false;
          break;
        }
      }

      // If ''removing_x'' is valid, it is safe to remove ''x''
      // from the original ''controlling''
      if(removing_x)
      {
        ctrl_update=true;
        break;
      }
    }
    // Update ''controlling'' or break the while loop
    if(ctrl_update)
    {
      controlling.swap(new_controlling);
    }
    else
      break;
  }
}

/*******************************************************************\

Function: collect_decisions_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void collect_decisions_rec(const exprt &src, std::set<exprt> &dest)
{
  if(src.id()==ID_address_of)
  {
    return;
  }

  if(src.type().id()==ID_bool)
  {
    if(src.is_constant())
    {
      // ignore me
    }
    else if(src.id()==ID_not)
    {
      collect_decisions_rec(src.op0(), dest);
    }
    else
    {
      dest.insert(src);
    }
  }
  else
  {
    for(const auto & op : src.operands())
      collect_decisions_rec(op, dest);
  }
}

/*******************************************************************\

Function: collect_decisions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::set<exprt> collect_decisions(const exprt &src)
{
  std::set<exprt> result;
  collect_decisions_rec(src, result);
  return result;
}

/*******************************************************************\

Function: collect_decisions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::set<exprt> collect_decisions(
  const goto_programt::const_targett t)
{
  switch(t->type)
  {
  case GOTO:
  case ASSERT:
    return collect_decisions(t->guard);

  case ASSIGN:
  case FUNCTION_CALL:
    return collect_decisions(t->code);

  default: {}
  }

  return std::set<exprt>();
}

/*******************************************************************\

Function: instrument_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_assertion(
  goto_programt::instructionst::iterator &insn)
{
  if(insn->is_assert())
  {
    insn->guard=false_exprt();
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);
  }
}

/*******************************************************************\

Function: instrument_cover

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_cover(
  goto_programt::instructionst::iterator &insn)
{
  if(insn->is_function_call())
  {
    const code_function_callt &code_function_call=
      to_code_function_call(insn->code);
    if(code_function_call.function().id()==ID_symbol &&
       to_symbol_expr(code_function_call.function()).get_identifier()==
       "__CPROVER_cover" &&
       code_function_call.arguments().size()==1)
    {
      const exprt c=code_function_call.arguments()[0];
      std::string comment="condition `"+from_expr(ns, "", c)+"'";
      insn->guard=not_exprt(c);
      insn->type=ASSERT;
      insn->code.clear();
      insn->source_location.set_comment(comment);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);
    }
  }
  else if(insn->is_assert())
    insn->make_skip();
}

/*******************************************************************\

Function: instrument_location

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_location(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program,
  basic_blockst &basic_blocks,
  std::set<unsigned> &blocks_done)
{
  if(insn->is_assert())
    insn->make_skip();

  unsigned block_nr=basic_blocks[insn];
  if(blocks_done.insert(block_nr).second)
  {
    std::string b=i2string(block_nr);
    std::string id=id2string(insn->function)+"#"+b;
    source_locationt source_location=
      basic_blocks.source_location_map[block_nr];

    if(!source_location.get_file().empty() &&
       source_location.get_file()[0]!='<')
    {
      std::string comment="block "+b;
      goto_program.insert_before_swap(insn);
      insn->make_assertion(false_exprt());
      insn->source_location=source_location;
      insn->source_location.set_comment(comment);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);

      insn++;
    }
  }
}

/*******************************************************************\

Function: instrument_branch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_branch(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program,
  basic_blockst &basic_blocks)
{
  if(insn->is_assert())
    insn->make_skip();

  if(insn==goto_program.instructions.begin())
  {
    // we want branch coverage to imply 'entry point of function'
    // coverage
    std::string comment=
      "function "+id2string(insn->function)+" entry point";

    source_locationt source_location=insn->source_location;

    goto_programt::targett t=goto_program.insert_before(insn);
    t->make_assertion(false_exprt());
    t->source_location=source_location;
    t->source_location.set_comment(comment);
    t->source_location.set(ID_coverage_criterion, coverage_criterion);
    t->source_location.set_property_class(property_class);
  }

  if(insn->is_goto() && !insn->guard.is_true())
  {
    std::string b=i2string(basic_blocks[insn]);
    std::string true_comment=
      "function "+id2string(insn->function)+" block "+b+" branch true";
    std::string false_comment=
      "function "+id2string(insn->function)+" block "+b+" branch false";

    exprt guard=insn->guard;
    source_locationt source_location=insn->source_location;

    goto_program.insert_before_swap(insn);
    insn->make_assertion(not_exprt(guard));
    insn->source_location=source_location;
    insn->source_location.set_comment(true_comment);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);

    goto_program.insert_before_swap(insn);
    insn->make_assertion(guard);
    insn->source_location=source_location;
    insn->source_location.set_comment(false_comment);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);

    insn++;
    insn++;
  }
}

/*******************************************************************\

Function: instrument_condition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_condition(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program)
{
  if(insn->is_assert())
    insn->make_skip();

  // Conditions are all atomic predicates in the programs.
  {
    const std::set<exprt> conditions=collect_conditions(insn);

    const source_locationt source_location=insn->source_location;

    for(const auto & c : conditions)
    {
      const std::string c_string=from_expr(ns, "", c);

      const std::string comment_t="condition `"+c_string+"' true";
      goto_program.insert_before_swap(insn);
      insn->make_assertion(c);
      insn->source_location=source_location;
      insn->source_location.set_comment(comment_t);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);

      const std::string comment_f="condition `"+c_string+"' false";
      goto_program.insert_before_swap(insn);
      insn->make_assertion(not_exprt(c));
      insn->source_location=source_location;
      insn->source_location.set_comment(comment_f);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);
    }

    for(std::size_t i=0; i<conditions.size()*2; i++)
      insn++;
  }
}

/*******************************************************************\

Function: instrument_decision

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_decision(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program)
{
  if(insn->is_assert())
    insn->make_skip();

  // Decisions are maximal Boolean combinations of conditions.
  {
    const std::set<exprt> decisions=collect_decisions(insn);

    const source_locationt source_location=insn->source_location;

    for(const auto & d : decisions)
    {
      const std::string d_string=from_expr(ns, "", d);

      const std::string comment_t="decision `"+d_string+"' true";
      goto_program.insert_before_swap(insn);
      insn->make_assertion(d);
      insn->source_location=source_location;
      insn->source_location.set_comment(comment_t);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);

      const std::string comment_f="decision `"+d_string+"' false";
      goto_program.insert_before_swap(insn);
      insn->make_assertion(not_exprt(d));
      insn->source_location=source_location;
      insn->source_location.set_comment(comment_f);
      insn->source_location.set(ID_coverage_criterion, coverage_criterion);
      insn->source_location.set_property_class(property_class);
    }

    for(std::size_t i=0; i<decisions.size()*2; i++)
      insn++;
  }
}

/*******************************************************************\

Function: instrument_mcdc

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_mcdc(
  goto_programt::instructionst::iterator &insn,
  goto_programt &goto_program,
  basic_blockst &basic_blocks,
  std::set<unsigned> &blocks_done)
{
  if(insn->is_assert())
    insn->make_skip();

  // 1. Each entry and exit point is invoked
  // 2. Each decision takes every possible outcome
  // 3. Each condition in a decision takes every possible outcome
  // 4. Each condition in a decision is shown to independently
  //    affect the outcome of the decision.

  const std::set<exprt> conditions=collect_conditions(insn);
  const std::set<exprt> decisions=collect_decisions(insn);

  std::set<exprt> both;
  std::set_union(conditions.begin(), conditions.end(),
                 decisions.begin(), decisions.end(),
                 inserter(both, both.end()));

  const source_locationt source_location=insn->source_location;

  for(const auto & p : both)
  {
    bool is_decision=decisions.find(p)!=decisions.end();
    bool is_condition=conditions.find(p)!=conditions.end();

    std::string description=
      (is_decision && is_condition)?"decision/condition":
      is_decision?"decision":"condition";

    std::string p_string=from_expr(ns, "", p);

    std::string comment_t=description+" `"+p_string+"' true";
    goto_program.insert_before_swap(insn);
    insn->make_assertion(not_exprt(p));
    insn->source_location=source_location;
    insn->source_location.set_comment(comment_t);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);

    std::string comment_f=description+" `"+p_string+"' false";
    goto_program.insert_before_swap(insn);
    insn->make_assertion(p);
    insn->source_location=source_location;
    insn->source_location.set_comment(comment_f);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);
  }

  bool boundary_values_analysis=
       criteria.find(coverage_criteriont::BOUNDARY)!=criteria.end();
  std::set<exprt> controlling;
  for(auto &dec : decisions)
  {
    std::set<exprt> ctrl=collect_mcdc_controlling_nested({dec});
    if(boundary_values_analysis)
    {
      auto res=decision_expansion(dec);
      ctrl.insert(res.begin(), res.end());
    }
    remove_repetition(ctrl);
    minimize_mcdc_controlling(ctrl, dec);
    controlling.insert(ctrl.begin(), ctrl.end());
  }

  if(boundary_values_analysis)
  {
    std::set<exprt> boundary_controlling;
    for(auto &x : controlling)
    {
      auto res=non_ordered_expr_expansion(x);
      boundary_controlling.insert(res.begin(), res.end());
    }
    controlling=boundary_controlling;
    remove_repetition(controlling);
  }

  for(const auto & p : controlling)
  {
    std::string p_string=from_expr(ns, "", p);

    std::string description=
      "MC/DC independence condition `"+p_string+"'";

    goto_program.insert_before_swap(insn);
    insn->make_assertion(not_exprt(p));
    insn->source_location=source_location;
    insn->source_location.set_comment(description);
    insn->source_location.set(ID_coverage_criterion, coverage_criterion);
    insn->source_location.set_property_class(property_class);
  }

  for(std::size_t i=0; i<both.size()*2+controlling.size(); i++)
    insn++;
}

/*******************************************************************\

Function: instrument_cover_goals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_cover_goals(
  goto_programt &goto_program)
{
  basic_blockst basic_blocks(goto_program);
  std::set<unsigned> blocks_done;

  // ignore if built-in library
  if(!goto_program.instructions.empty() &&
     has_prefix(
       id2string(
         goto_program.instructions.front().source_location.get_file()),
         "<builtin-library-"))
    return;

  for(const auto &criterion : criteria)
  {
    coverage_criterion=as_string(criterion);
    property_class="coverage";

    Forall_goto_program_instructions(i_it, goto_program)
    {
      switch(criterion)
      {
      case coverage_criteriont::ASSERTION:
        // turn into 'assert(false)' to avoid simplification
        instrument_assertion(i_it);
        break;

      case coverage_criteriont::COVER:
        // turn __CPROVER_cover(x) into 'assert(!x)'
        instrument_cover(i_it);
        break;

      case coverage_criteriont::LOCATION:
        instrument_location(i_it, goto_program, basic_blocks, blocks_done);
        break;

      case coverage_criteriont::BRANCH:
        instrument_branch(i_it, goto_program, basic_blocks);
        break;

      case coverage_criteriont::CONDITION:
        instrument_condition(i_it, goto_program);
        break;

      case coverage_criteriont::DECISION:
        instrument_decision(i_it, goto_program);
        break;

      case coverage_criteriont::MCDC:
        instrument_mcdc(i_it, goto_program, basic_blocks, blocks_done);
        break;

      case coverage_criteriont::PATH:
        if(i_it->is_assert())
          i_it->make_skip();
        break;

      default: {}
      }
    }
  }
}

/*******************************************************************\

Function: instrument_cover_goals

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void instrument_cover_goalst::instrument_cover_goals(
  goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
  {
    if(f_it->first==ID__start ||
       f_it->first=="__CPROVER_initialize")
      continue;

    instrument_cover_goals(f_it->second.body);
  }
}
