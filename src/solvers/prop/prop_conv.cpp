/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <map>

#include <std_expr.h>
#include <symbol.h>

#include "prop_conv.h"

//#define DEBUG

/*******************************************************************\

Function: prop_convt::literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool prop_convt::literal(const exprt &expr, literalt &dest) const
{
  assert(expr.type().id()==ID_bool);

  if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=
      to_symbol_expr(expr).get_identifier();

    symbolst::const_iterator result=symbols.find(identifier);

    if(result==symbols.end()) return true;
    dest=result->second;
    return false;
  }

  throw "found no literal for expression";
}

/*******************************************************************\

Function: prop_convt::get_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt prop_convt::get_literal(const irep_idt &identifier)
{
  std::pair<symbolst::iterator, bool> result=
    symbols.insert(std::pair<irep_idt, literalt>(identifier, literalt()));

  if(!result.second)
    return result.first->second;

  // produce new variable
  literalt literal=prop.new_variable();
  
  // set the name of the new variable
  prop.set_variable_name(literal, id2string(identifier));

  // insert
  result.first->second=literal;

  return literal;
}

/*******************************************************************\

Function: prop_convt::get_bool

  Inputs:

 Outputs:

 Purpose: get a boolean value from counter example if not valid

\*******************************************************************/

bool prop_convt::get_bool(const exprt &expr, tvt &value) const
{
  // trivial cases

  if(expr.is_true())
  {
    value=tvt(true);
    return false;
  }
  else if(expr.is_false())
  {
    value=tvt(false);
    return false;
  }
  else if(expr.id()==ID_symbol)
  {
    symbolst::const_iterator result=
      symbols.find(to_symbol_expr(expr).get_identifier());
      
    if(result==symbols.end()) return true;

    value=prop.l_get(result->second);
    return false;
  }

  // sub-expressions

  if(expr.id()==ID_not)
  {
    if(expr.type().id()==ID_bool &&
       expr.operands().size()==1)
    {
      if(get_bool(expr.op0(), value)) return true;
      value=!value;
      return false;
    }
  }
  else if(expr.id()==ID_and || expr.id()==ID_or)
  {
    if(expr.type().id()==ID_bool &&
       expr.operands().size()>=1)
    {
      value=tvt(expr.id()==ID_and);

      forall_operands(it, expr)
      {
        tvt tmp;
        if(get_bool(*it, tmp)) return true;

        if(expr.id()==ID_and)
        {
          if(tmp.is_false()) { value=tvt(false); return false; }

          value=value && tmp;
        }
        else // or
        {
          if(tmp.is_true()) { value=tvt(true); return false; }

          value=value || tmp;
        }
      }

      return false;
    }
  }

  // check cache

  cachet::const_iterator cache_result=cache.find(expr);
  if(cache_result==cache.end()) return true;

  value=prop.l_get(cache_result->second);
  return false;
}

/*******************************************************************\

Function: prop_convt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt prop_convt::convert(const exprt &expr)
{
  if(!use_cache || 
     expr.id()==ID_symbol ||
     expr.id()==ID_constant)
    return convert_bool(expr);

  // check cache first

  std::pair<cachet::iterator, bool> result=
    cache.insert(std::pair<exprt, literalt>(expr, literalt()));

  if(!result.second)
    return result.first->second;

  literalt literal=convert_bool(expr);

  // insert into cache

  result.first->second=literal;

  #if 0
  std::cout << literal << "=" << expr << std::endl;
  #endif

  return literal;
}

/*******************************************************************\

Function: prop_convt::convert_bool

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt prop_convt::convert_bool(const exprt &expr)
{
  if(expr.type().id()!=ID_bool)
  {
    std::string msg="prop_convt::convert_bool got "
                    "non-boolean expression:\n";
    msg+=expr.to_string();
    throw msg;
  }

  const exprt::operandst &op=expr.operands();

  if(expr.is_constant())
  {
    if(expr.is_true())
      return const_literal(true);
    else if(expr.is_false())
      return const_literal(false);
    else
      throw "unknown boolean constant: "+expr.to_string();
  }
  else if(expr.id()==ID_symbol)
  {
    return get_literal(expr.get(ID_identifier));
  }
  else if(expr.id()==ID_literal)
  {
    literalt l;
    l.set(atoi(expr.get(ID_literal).c_str()));
    return l;
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    return prop.new_variable();
  }
  else if(expr.id()==ID_implies)
  {
    if(op.size()!=2)
      throw "implication takes two operands";

    return prop.limplies(convert(op[0]), convert(op[1]));
  }
  else if(expr.id()==ID_if)
  {
    if(op.size()!=3)
      throw "if takes three operands";

    return prop.lselect(convert(op[0]), convert(op[1]), convert(op[2]));
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    if(op.size()<2)
      throw "constraint_select_one takes at least two operands";

    std::vector<literalt> op_bv;
    op_bv.resize(op.size());

    unsigned i=0;
    forall_operands(it, expr)
      op_bv[i++]=convert(*it);

    // add constraints

    bvt b;
    b.reserve(op_bv.size()-1);

    for(unsigned i=1; i<op_bv.size(); i++)
      b.push_back(prop.lequal(op_bv[0], op_bv[i]));

    prop.l_set_to_true(prop.lor(b));

    return op_bv[0];
  }
  else if(expr.id()==ID_or || expr.id()==ID_and || expr.id()==ID_xor ||
          expr.id()==ID_nor || expr.id()==ID_nand)
  {
    if(op.size()==0)
      throw "operator "+expr.id_string()+" takes at least one operand";

    bvt bv;

    forall_expr(it, op)
      bv.push_back(convert(*it));

    if(!bv.empty())
    {
      if(expr.id()==ID_or)
        return prop.lor(bv);
      else if(expr.id()==ID_nor)
        return prop.lnot(prop.lor(bv));
      else if(expr.id()==ID_and)
        return prop.land(bv);
      else if(expr.id()==ID_nand)
        return prop.lnot(prop.land(bv));
      else if(expr.id()==ID_xor) 
        return prop.lxor(bv);
    }
  }
  else if(expr.id()==ID_not)
  {
    if(op.size()!=1)
      throw "not takes one operand";

    return prop.lnot(convert(op[0]));
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    if(op.size()!=2)
      throw "equality takes two operands";

    bool equal=(expr.id()==ID_equal);

    if(op[0].type().id()==ID_bool &&
       op[1].type().id()==ID_bool)
    {
      literalt tmp1=convert(op[0]),
               tmp2=convert(op[1]);
      return
        equal?prop.lequal(tmp1, tmp2):prop.lxor(tmp1, tmp2);
    }
  }

  return convert_rest(expr);
}

/*******************************************************************\

Function: prop_convt::convert_rest

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt prop_convt::convert_rest(const exprt &expr)
{
  // fall through
  ignoring(expr);
  return prop.new_variable();
}

/*******************************************************************\

Function: prop_convt::set_equality_to_true

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool prop_convt::set_equality_to_true(const exprt &expr)
{
  if(!equality_propagation) return true;

  if(expr.operands().size()==2)
  {
    // optimization for constraint of the form
    // new_variable = value

    if(expr.op0().id()==ID_symbol)
    {
      const irep_idt &identifier=
        expr.op0().get(ID_identifier);

      literalt tmp=convert(expr.op1());

      std::pair<symbolst::iterator, bool> result=
        symbols.insert(std::pair<irep_idt, literalt>(identifier, tmp));

      if(result.second)
        return false; // ok, inserted!
        
      // nah, already there
    }
  }

  return true;
}

/*******************************************************************\

Function: prop_convt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_convt::set_to(const exprt &expr, bool value)
{
  if(expr.type().id()!=ID_bool)
  {
    std::string msg="prop_convt::set_to got "
                    "non-boolean expression:\n";
    msg+=expr.to_string();
    throw msg;
  }

  bool boolean=true;

  forall_operands(it, expr)
    if(it->type().id()!=ID_bool)
    {
      boolean=false;
      break;
    }

  if(boolean)
  {
    if(expr.id()==ID_not)
    {
      if(expr.operands().size()==1)
      {
        set_to(expr.op0(), !value);
        return;
      }
    }
    else
    {
      if(value)
      {
        // set_to_true

        if(expr.id()==ID_and)
        {
          forall_operands(it, expr)
            set_to_true(*it);

          return;
        }
        else if(expr.id()==ID_or)
        {
          if(expr.operands().size()>0)
          {
            bvt bv;
            bv.reserve(expr.operands().size());

            forall_operands(it, expr)
              bv.push_back(convert(*it));

            prop.lcnf(bv);
            return;
          }
        }
        else if(expr.id()==ID_implies)
        {
          if(expr.operands().size()==2)
          {
            bvt bv;
            bv.resize(2);
            bv[0]=prop.lnot(convert(expr.op0()));
            bv[1]=convert(expr.op1());
            prop.lcnf(bv);
            return;
          }
        }
        else if(expr.id()==ID_equal)
        {
          if(!set_equality_to_true(expr))
            return;
        }
      }
      else
      {
        // set_to_false
        if(expr.id()==ID_implies) // !(a=>b)  ==  (a && !b)
        {
          if(expr.operands().size()==2)
          {
            set_to_true(expr.op0());
            set_to_false(expr.op1());
          }
        }
        else if(expr.id()==ID_or) // !(a || b)  ==  (!a && !b)
        {
          forall_operands(it, expr)
            set_to_false(*it);
        }
      }
    }
  }

  // fall back to convert
  prop.l_set_to(convert(expr), value);
}

/*******************************************************************\

Function: prop_convt::ignoring

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_convt::ignoring(const exprt &expr)
{
  // fall through

  std::string msg="warning: ignoring "+expr.pretty();

  print(2, msg);
}

/*******************************************************************\

Function: prop_convt::post_process

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_convt::post_process()
{
}

/*******************************************************************\

Function: prop_convt::solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt prop_convt::dec_solve()
{
  post_process();

  print(7, "Solving with "+prop.solver_text());

  propt::resultt result=prop.prop_solve();

  switch(result)
  {
   case propt::P_SATISFIABLE: return D_SATISFIABLE;
   case propt::P_UNSATISFIABLE: return D_UNSATISFIABLE;
   default: return D_ERROR;
  }

  return D_ERROR;
}

/*******************************************************************\

Function: prop_convt::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt prop_convt::get(const exprt &expr) const
{
  tvt value;

  if(expr.type().id()==ID_bool &&
     !get_bool(expr, value))
  {
    switch(value.get_value())
    {
     case tvt::TV_TRUE:  return true_exprt();
     case tvt::TV_FALSE: return false_exprt();
     case tvt::TV_UNKNOWN: return false_exprt(); // default
    }
  }
  
  exprt tmp=expr;
  
  Forall_operands(it, tmp)
  {
    exprt tmp_op=get(*it);
    it->swap(tmp_op);
  }

  return tmp;
}

/*******************************************************************\

Function: prop_convt::print_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void prop_convt::print_assignment(std::ostream &out) const
{
  for(symbolst::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
    out << it->first << " = " << prop.l_get(it->second) << std::endl;
}

