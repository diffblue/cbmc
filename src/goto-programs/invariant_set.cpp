/*******************************************************************\

Module: Invariant Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <context.h>
#include <namespace.h>
#include <expr_util.h>
#include <bitvector.h>
#include <arith_tools.h>
#include <std_expr.h>
#include <simplify_expr.h>
#include <base_type.h>
#include <std_types.h>

#include <ansi-c/c_types.h>
#include <langapi/language_util.h>

#include "invariant_set.h"

/*******************************************************************\

Function: inv_object_storet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void inv_object_storet::output(std::ostream &out) const
{
  for(unsigned i=0; i<entries.size(); i++)
    out << "STORE " << i << ": " << to_string(i, "") << std::endl;
}

/*******************************************************************\

Function: inv_object_storet::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool inv_object_storet::get(const exprt &expr, unsigned &n)
{
  std::string s=build_string(expr);
  if(s=="") return true;
  
  // if it's a constant, we add it in any case
  if(is_constant(expr))
  {
    n=map.number(s);
    
    if(n>=entries.size())
    {
      entries.resize(n+1);
      entries[n].expr=expr;
      entries[n].is_constant=true;
    }
    
    return false;
  }

  return map.get_number(s, n);
}
  
/*******************************************************************\

Function: inv_object_storet::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned inv_object_storet::add(const exprt &expr)
{
  std::string s=build_string(expr);
  
  assert(s!="");

  unsigned n=map.number(s);
  
  if(n>=entries.size())
  {
    entries.resize(n+1);
    entries[n].expr=expr;
    entries[n].is_constant=is_constant(expr);
  }
  
  return n;
}
  
/*******************************************************************\

Function: inv_object_storet::is_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool inv_object_storet::is_constant(unsigned n) const
{
  assert(n<entries.size());
  return entries[n].is_constant;
}  

/*******************************************************************\

Function: inv_object_storet::is_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool inv_object_storet::is_constant(const exprt &expr) const
{
  return expr.is_constant() ||
         is_constant_address(expr);
}  

/*******************************************************************\

Function: inv_object_storet::build_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string inv_object_storet::build_string(const exprt &expr) const
{
  // we ignore some casts
  if(expr.id()==ID_typecast)
  {
    assert(expr.operands().size()==1);
    
    if(expr.type().id()==ID_signedbv ||
       expr.type().id()==ID_unsignedbv)
    {
      if(expr.op0().type().id()==ID_signedbv ||
         expr.op0().type().id()==ID_unsignedbv)
      {
        if(to_bitvector_type(expr.type()).get_width()>=
           to_bitvector_type(expr.op0().type()).get_width())
          return build_string(expr.op0());
      }
      else if(expr.op0().type().id()==ID_bool)
      {
        return build_string(expr.op0());
      }
    }
  }
  
  // we always track constants, but make sure they are uniquely
  // represented
  if(expr.is_constant())
  {
    // NULL?
    if(expr.type().id()==ID_pointer)
      if(expr.get(ID_value)==ID_NULL)
        return "0";
  
    mp_integer i;

    if(!to_integer(expr, i))
      return integer2string(i);
  }
  
  // we also like "address_of" and "reference_to"
  // if the object is constant
  if(is_constant_address(expr))
    return from_expr(ns, "", expr);
  
  if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    return build_string(expr.op0())+"."+expr.get_string(ID_component_name);
  }
  
  if(expr.id()==ID_symbol)
    return expr.get_string(ID_identifier);

  return "";
}

/*******************************************************************\

Function: invariant_sett::get_object

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool invariant_sett::get_object(
  const exprt &expr,
  unsigned &n) const
{
  assert(object_store!=NULL);
  return object_store->get(expr, n);
}

/*******************************************************************\

Function: inv_object_storet::is_constant_address

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool inv_object_storet::is_constant_address(const exprt &expr)
{
  if(expr.id()==ID_address_of)
    if(expr.operands().size()==1)
      return is_constant_address_rec(expr.op0());
  
  return false;
}

/*******************************************************************\

Function: inv_object_storet::is_constant_address_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool inv_object_storet::is_constant_address_rec(const exprt &expr)
{
  if(expr.id()==ID_symbol)
    return true;
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);
    return is_constant_address_rec(expr.op0());
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);
    if(expr.op1().is_constant())
      return is_constant_address_rec(expr.op0());
  }
  
  return false;
}

/*******************************************************************\

Function: invariant_sett::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::add(
  const std::pair<unsigned, unsigned> &p,
  ineq_sett &dest)
{
  eq_set.check_index(p.first);
  eq_set.check_index(p.second);

  // add all. Quadratic.
  unsigned f_r=eq_set.find(p.first);
  unsigned s_r=eq_set.find(p.second);
  
  for(unsigned f=0; f<eq_set.size(); f++)
    if(eq_set.find(f)==f_r)
      for(unsigned s=0; s<eq_set.size(); s++)
        if(eq_set.find(s)==s_r)
          dest.insert(std::pair<unsigned, unsigned>(f, s));
}

/*******************************************************************\

Function: invariant_sett::add_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::add_eq(const std::pair<unsigned, unsigned> &p)
{
  eq_set.make_union(p.first, p.second);

  // check if there is a contradiction with two constants
  unsigned r=eq_set.find(p.first);
  
  bool constant_seen=false;
  mp_integer c;
  
  for(unsigned i=0; i<eq_set.size(); i++)
    if(eq_set.find(i)==r)
      if(object_store->is_constant(i))
      {
        if(constant_seen)
        {
          // contradiction
          make_false();
          return;
        }
        else 
          constant_seen=true;
      }

  // replicate <= and != constraints
  
  for(ineq_sett::const_iterator it=le_set.begin();
      it!=le_set.end();
      it++)
    add_eq(le_set, p, *it);

  for(ineq_sett::const_iterator it=ne_set.begin();
      it!=ne_set.end();
      it++)
    add_eq(ne_set, p, *it);
}

/*******************************************************************\

Function: invariant_sett::add_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::add_eq(
  ineq_sett &dest,
  const std::pair<unsigned, unsigned> &eq,
  const std::pair<unsigned, unsigned> &ineq)
{
  std::pair<unsigned, unsigned> n;

  // uhuh. Need to try all pairs

  if(eq.first==ineq.first)
  {
    n=ineq;
    n.first=eq.second; 
    dest.insert(n);
  }
  
  if(eq.first==ineq.second)
  {
    n=ineq;
    n.second=eq.second;
    dest.insert(n);
  }
  
  if(eq.second==ineq.first)
  {
    n=ineq;
    n.first=eq.first; 
    dest.insert(n);
  }
  
  if(eq.second==ineq.second)
  {
    n=ineq;
    n.second=eq.first;
    dest.insert(n);
  }
}

/*******************************************************************\

Function: invariant_sett::is_eq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt invariant_sett::is_eq(std::pair<unsigned, unsigned> p) const
{
  std::pair<unsigned, unsigned> s=p;
  std::swap(s.first, s.second);
  
  if(has_eq(p))
    return tvt(true);
    
  if(has_ne(p) || has_ne(s))
    return tvt(false);

  return tvt(tvt::TV_UNKNOWN);
}
  
/*******************************************************************\

Function: invariant_sett::is_le

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt invariant_sett::is_le(std::pair<unsigned, unsigned> p) const
{
  std::pair<unsigned, unsigned> s=p;
  std::swap(s.first, s.second);
  
  if(has_eq(p))
    return tvt(true);
  
  if(has_le(p))
    return tvt(true);
    
  if(has_le(s))
    if(has_ne(s) || has_ne(p))
      return tvt(false);
    
  return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: invariant_sett::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::output(
  const irep_idt &identifier,
  std::ostream &out) const
{
  if(is_false)
  {
    out << "FALSE" << std::endl;
    return;
  }

  assert(object_store!=NULL);

  for(unsigned i=0; i<eq_set.size(); i++)
    if(eq_set.is_root(i) &&
       eq_set.count(i)>=2)
    {
      bool first=true;
      for(unsigned j=0; j<eq_set.size(); j++)
        if(eq_set.find(j)==i)
        {
          if(first)
            first=false;
          else
            out << " = ";

          out << to_string(j, identifier);
        }
        
      out << std::endl;
    }

  for(bounds_mapt::const_iterator it=bounds_map.begin();
      it!=bounds_map.end();
      it++)
  {
    out << to_string(it->first, identifier)
        << " in " << it->second
        << std::endl;
  }

  for(ineq_sett::const_iterator it=le_set.begin();
      it!=le_set.end();
      it++)
  {
    out << to_string(it->first, identifier)
        << " <= " << to_string(it->second, identifier)
        << std::endl;
  }

  for(ineq_sett::const_iterator it=ne_set.begin();
      it!=ne_set.end();
      it++)
  {
    out << to_string(it->first, identifier)
        << " != " << to_string(it->second, identifier)
        << std::endl;
  }
}

/*******************************************************************\

Function: invariant_sett::strengthen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::add_type_bounds(const exprt &expr, const typet &type)
{
  if(expr.type()==type) return;

  if(type.id()==ID_unsignedbv)
  {
    unsigned op_width=to_unsignedbv_type(type).get_width();

    if(op_width<=8)
    {
      unsigned a;
      if(get_object(expr, a)) return;
      
      add_bounds(a, boundst(0, power(2, op_width)-1));
    }
  }
}

/*******************************************************************\

Function: invariant_sett::strengthen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::strengthen(const exprt &expr)
{
  exprt tmp(expr);
  nnf(tmp);
  strengthen_rec(tmp);
}

/*******************************************************************\

Function: invariant_sett::strengthen_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::strengthen_rec(const exprt &expr)
{
  if(expr.type().id()!=ID_bool)
    throw "non-Boolean argument to strengthen()";

  #if 0
  std::cout << "S: " << from_expr(*ns, "", expr) << std::endl;
  #endif
    
  if(is_false)
  {
    // we can't get any stronger
    return;
  }
  
  if(expr.is_true())
  {
    // do nothing, it's useless
  }
  else if(expr.is_false())
  {
    // wow, that's strong
    make_false();
  }
  else if(expr.id()==ID_not)
  {
    // give up, we expect NNF
  }
  else if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      strengthen_rec(*it);
  }
  else if(expr.id()=="<=" ||
          expr.id()=="<")
  {
    assert(expr.operands().size()==2);
    
    // special rule: x <= (a & b)
    // implies:      x<=a && x<=b

    if(expr.op1().id()==ID_bitand)
    {
      const exprt &bitand_op=expr.op1();
      
      forall_operands(it, bitand_op)
      {
        exprt tmp(expr);
        tmp.op1()=*it;
        strengthen_rec(tmp);
      }
      
      return;
    }

    std::pair<unsigned, unsigned> p;
    
    if(get_object(expr.op0(), p.first) ||
       get_object(expr.op1(), p.second))
      return;

    mp_integer i0, i1;
    bool have_i0=!to_integer(expr.op0(), i0);
    bool have_i1=!to_integer(expr.op1(), i1);
    
    if(expr.id()=="<=")
    {
      if(have_i0)
        add_bounds(p.second, lower_interval(i0));
      else if(have_i1)
        add_bounds(p.first, upper_interval(i1));
      else
        add_le(p);
    }
    else if(expr.id()=="<")
    {
      if(have_i0)
        add_bounds(p.second, lower_interval(i0+1));
      else if(have_i1)
        add_bounds(p.first, upper_interval(i1-1));
      else
      {
        add_le(p);
        add_ne(p);
      }
    }
    else
      assert(false);
  }
  else if(expr.id()=="=")
  {
    assert(expr.operands().size()==2);
    
    const typet &op_type=ns->follow(expr.op0().type());
    
    if(op_type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(op_type);
  
      const struct_typet::componentst &c=struct_type.components();
  
      exprt lhs_member_expr(ID_member);
      exprt rhs_member_expr(ID_member);
      lhs_member_expr.copy_to_operands(expr.op0());
      rhs_member_expr.copy_to_operands(expr.op1());
  
      for(struct_typet::componentst::const_iterator
          it=c.begin();
          it!=c.end();
          it++)
      {
        const irep_idt &component_name=it->get(ID_name);

        lhs_member_expr.set(ID_component_name, component_name);
        rhs_member_expr.set(ID_component_name, component_name);
        lhs_member_expr.type()=it->type();
        rhs_member_expr.type()=it->type();

        equal_exprt equality;
        equality.lhs()=lhs_member_expr;
        equality.rhs()=rhs_member_expr;
        
        // recursive call
        strengthen_rec(equality);
      }
      
      return;
    }
    
    // special rule: x = (a & b)
    // implies:      x<=a && x<=b

    if(expr.op1().id()==ID_bitand)
    {
      const exprt &bitand_op=expr.op1();
      
      forall_operands(it, bitand_op)
      {
        exprt tmp(expr);
        tmp.op1()=*it;
        tmp.id("<=");
        strengthen_rec(tmp);
      }
      
      return;
    }
    else if(expr.op0().id()==ID_bitand)
    {
      exprt tmp(expr);
      std::swap(tmp.op0(), tmp.op1());
      strengthen_rec(tmp);
      return;
    }
    
    // special rule: x = (type) y
    if(expr.op1().id()==ID_typecast)
    {
      assert(expr.op1().operands().size()==1);
      add_type_bounds(expr.op0(), expr.op1().op0().type());
    }
    else if(expr.op0().id()==ID_typecast)
    {
      assert(expr.op0().operands().size()==1);
      add_type_bounds(expr.op1(), expr.op0().op0().type());
    }
    
    std::pair<unsigned, unsigned> p, s;
    
    if(get_object(expr.op0(), p.first) ||
       get_object(expr.op1(), p.second))
      return;

    mp_integer i;

    if(!to_integer(expr.op0(), i))
      add_bounds(p.second, boundst(i));
    else if(!to_integer(expr.op1(), i))
      add_bounds(p.first, boundst(i));

    s=p;
    std::swap(s.first, s.second);

    // contradiction?
    if(has_ne(p) || has_ne(s))
      make_false();
    else if(!has_eq(p))
      add_eq(p);
  }
  else if(expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);
    
    std::pair<unsigned, unsigned> p;
    
    if(get_object(expr.op0(), p.first) ||
       get_object(expr.op1(), p.second))
      return;
      
    // check if this is a contradiction
    if(has_eq(p))
      make_false();
    else
      add_ne(p);
  }
}

/*******************************************************************\

Function: invariant_sett::implies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt invariant_sett::implies(const exprt &expr) const
{
  exprt tmp(expr);
  nnf(tmp);
  return implies_rec(tmp);
}
    
/*******************************************************************\

Function: invariant_sett::implies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt invariant_sett::implies_rec(const exprt &expr) const
{
  if(expr.type().id()!=ID_bool)
    throw "implies: non-Boolean expression";
    
  #if 0
  std::cout << "I: " << from_expr(*ns, "", expr) << std::endl;
  #endif
  
  if(is_false) // can't get any stronger
    return tvt(true);

  if(expr.is_true())
    return tvt(true);
  else if(expr.id()==ID_not)
  {
    // give up, we expect NNF
  }
  else if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      if(implies_rec(*it)!=tvt(true))
        return tvt(tvt::TV_UNKNOWN);
      
    return tvt(true);
  }
  else if(expr.id()==ID_or)
  {
    forall_operands(it, expr)
      if(implies_rec(*it)==tvt(true))
        return tvt(true);
  }
  else if(expr.id()=="<=" ||
          expr.id()=="<" ||
          expr.id()=="=" ||
          expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);

    std::pair<unsigned, unsigned> p;
    
    bool ob0=get_object(expr.op0(), p.first);
    bool ob1=get_object(expr.op1(), p.second);
    
    if(ob0 || ob1) return tvt(tvt::TV_UNKNOWN);
    
    tvt r;
    
    if(expr.id()=="<=")
    {
      r=is_le(p);
      if(!r.is_unknown()) return r;
      
      boundst b0, b1;
      get_bounds(p.first, b0);
      get_bounds(p.second, b1);
      
      return b0<=b1;
    }
    else if(expr.id()=="<")
    {
      r=is_lt(p);
      if(!r.is_unknown()) return r;

      boundst b0, b1;
      get_bounds(p.first, b0);
      get_bounds(p.second, b1);
      
      return b0<b1;
    }
    else if(expr.id()=="=")
      return is_eq(p);
    else if(expr.id()==ID_notequal)
      return is_ne(p);
    else
      assert(false);
  }

  return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: invariant_sett::get_bounds

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::get_bounds(unsigned a, boundst &bounds) const
{
  // unbounded
  bounds=boundst();

  {
    const exprt &e_a=object_store->get_expr(a);
    mp_integer tmp;
    if(!to_integer(e_a, tmp))
    {
      bounds=boundst(tmp);
      return;
    }
    
    if(e_a.type().id()==ID_unsignedbv)
      bounds=lower_interval(mp_integer(0));
  }

  bounds_mapt::const_iterator it=bounds_map.find(a);
  
  if(it!=bounds_map.end()) bounds=it->second;
}

/*******************************************************************\

Function: invariant_sett::nnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::nnf(exprt &expr, bool negate)
{
  if(expr.type().id()!=ID_bool)
    throw "nnf: non-Boolean expression";

  if(expr.is_true())
  {
    if(negate) expr.make_false();
  }
  else if(expr.is_false())
  {
    if(negate) expr.make_true();
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);
    nnf(expr.op0(), !negate);
    exprt tmp;
    tmp.swap(expr.op0());
    expr.swap(tmp);
  }
  else if(expr.id()==ID_and)
  {
    if(negate) expr.id(ID_or);
    
    Forall_operands(it, expr)
      nnf(*it, negate);
  }
  else if(expr.id()==ID_or)
  {
    if(negate) expr.id(ID_and);
    
    Forall_operands(it, expr)
      nnf(*it, negate);
  }
  else if(expr.id()==ID_typecast)
  {
    assert(expr.operands().size()==1);

    if(expr.op0().type().id()==ID_unsignedbv ||
       expr.op0().type().id()==ID_signedbv)
    {
      equal_exprt tmp;
      tmp.lhs()=expr.op0();
      tmp.rhs()=gen_zero(expr.op0().type());
      nnf(tmp, !negate);
      expr.swap(tmp);
    }
    else
    {
      if(negate) expr.make_not();
    }
  }
  else if(expr.id()=="<=")
  {
    if(negate)
    {
      // !a<=b <-> !b=>a <-> b<a
      expr.id("<");
      std::swap(expr.op0(), expr.op1());
    }
  }
  else if(expr.id()=="<")
  {
    if(negate)
    {
      // !a<b <-> !b>a <-> b<=a
      expr.id("<=");
      std::swap(expr.op0(), expr.op1());
    }
  }
  else if(expr.id()==">=")
  {
    if(negate)
      expr.id("<");
    else
    {
      expr.id("<=");
      std::swap(expr.op0(), expr.op1());
    }
  }
  else if(expr.id()==">")
  {
    if(negate)
      expr.id("<=");
    else
    {
      expr.id("<");
      std::swap(expr.op0(), expr.op1());
    }
  }
  else if(expr.id()=="=")
  {
    if(negate) expr.id(ID_notequal);
  }
  else if(expr.id()==ID_notequal)
  {
    if(negate) expr.id("=");
  }
  else
  {
    if(negate)
      expr.make_not();
  }
}

/*******************************************************************\

Function: invariant_sett::simplify

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::simplify(
  exprt &expr) const
{
  if(expr.id()==ID_address_of)
    return;

  Forall_operands(it, expr)
    simplify(*it);

  if(expr.id()==ID_symbol ||
     expr.id()==ID_member)
  {
    exprt tmp=get_constant(expr);
    if(tmp.is_not_nil())
      expr.swap(tmp);
  }
}

/*******************************************************************\

Function: invariant_sett::get_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt invariant_sett::get_constant(const exprt &expr) const
{
  unsigned a;

  if(!get_object(expr, a))
  {  
    // bounds?
    bounds_mapt::const_iterator it=bounds_map.find(a);
  
    if(it!=bounds_map.end())
    {
      if(it->second.singleton())
        return from_integer(it->second.get_lower(), expr.type());
    }

    unsigned r=eq_set.find(a);

    // is it a constant?
    for(unsigned i=0; i<eq_set.size(); i++)
      if(eq_set.find(i)==r)
      {
        const exprt &e=object_store->get_expr(i);
        
        if(e.is_constant())
        {
          mp_integer value;
          assert(!to_integer(e, value));
          
          if(expr.type().id()==ID_pointer)
          {
            if(value==0)
            {
              exprt tmp(ID_constant, expr.type());
              tmp.set(ID_value, ID_NULL);
              return tmp;
            }
          }
          else
            return from_integer(value, expr.type());
        }
        else if(object_store->is_constant_address(e))
        {
          if(e.type()==expr.type())
            return e;
            
          exprt tmp(ID_typecast, expr.type());
          tmp.copy_to_operands(e);
          return tmp;
        }
      }
  }
  
  return static_cast<const exprt &>(get_nil_irep());
}

/*******************************************************************\

Function: inv_object_storet::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string inv_object_storet::to_string(
  unsigned a,
  const irep_idt &identifier) const
{
  //return from_expr(ns, "", get_expr(a));
  return id2string(map[a]);
}

/*******************************************************************\

Function: invariant_sett::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string invariant_sett::to_string(
  unsigned a,
  const irep_idt &identifier) const
{
  assert(object_store!=NULL);
  return object_store->to_string(a, identifier);
}

/*******************************************************************\

Function: invariant_sett::make_union

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool invariant_sett::make_union(const invariant_sett &other)
{
  if(other.threaded &&
     !threaded)
  {
    make_threaded();
    return true; // change
  }
  
  if(threaded)
    return false; // no change

  if(other.is_false)
    return false; // no change
    
  if(is_false)
  {
    // copy
    is_false=false;
    eq_set=other.eq_set;
    le_set=other.le_set;
    ne_set=other.ne_set;
    bounds_map=other.bounds_map;
    
    return true; // change
  }
  
  // equalities first
  unsigned old_eq_roots=eq_set.count_roots();
  
  eq_set.intersection(other.eq_set);

  // inequalities
  unsigned old_ne_set=ne_set.size();
  unsigned old_le_set=le_set.size();
  
  intersection(ne_set, other.ne_set);
  intersection(le_set, other.le_set);
  
  // bounds
  if(make_union_bounds_map(other.bounds_map))
    return true;

  if(old_eq_roots!=eq_set.count_roots()) return true;
  if(old_ne_set!=ne_set.size()) return true;
  if(old_le_set!=le_set.size()) return true;
  
  return false; // no change
}

/*******************************************************************\

Function: invariant_sett::make_union_bounds_map

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool invariant_sett::make_union_bounds_map(const bounds_mapt &other)
{
  bool changed=false;
  
  for(bounds_mapt::iterator
      it=bounds_map.begin();
      it!=bounds_map.end();
      ) // no it++
  {
    bounds_mapt::const_iterator o_it=other.find(it->first);

    if(o_it==other.end())
    {
      bounds_mapt::iterator next(it);
      next++;
      bounds_map.erase(it);
      it=next;
      changed=true;
    }
    else
    {
      boundst old(it->second);
      it->second.approx_union_with(o_it->second);
      if(!(it->second==old).is_true()) changed=true;
      it++;
    }
  }
  
  return changed;
}

/*******************************************************************\

Function: invariant_sett::modifies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::modifies(unsigned a)
{
  eq_set.isolate(a);
  remove(ne_set, a);
  remove(le_set, a);
  bounds_map.erase(a);
}

/*******************************************************************\

Function: invariant_sett::modifies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::modifies(const exprt &lhs)
{
  if(lhs.id()==ID_symbol ||
     lhs.id()==ID_member)
  {
    unsigned a;
    if(!get_object(lhs, a)) modifies(a);
  }
  else if(lhs.id()==ID_index)
  {
    // we don't track arrays
  }
  else if(lhs.id()==ID_dereference)
  {
    // be very, very conservative for now
    make_true();
  }
  else if(lhs.id()=="object_value")
  {
    // be very, very conservative for now
    make_true();
  }
  else if(lhs.id()==ID_if)
  {
    // we just assume both are changed
    assert(lhs.operands().size()==3);
    modifies(lhs.op1());
    modifies(lhs.op2());
  }
  else if(lhs.id()==ID_typecast)
  {
    // just go down
    assert(lhs.operands().size()==1);
    modifies(lhs.op0());
  }
  else if(lhs.id()=="valid_object")
  {
  }
  else if(lhs.id()=="dynamic_size")
  {
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    // just go down
    assert(lhs.operands().size()==2);
    modifies(lhs.op0());
  }
  else if(lhs.id()=="NULL-object" ||
          lhs.id()=="is_zero_string" ||
          lhs.id()=="zero_string" ||
          lhs.id()=="zero_string_length")
  {
    // ignore
  }
  else
    throw "modifies: unexpected lhs: "+lhs.id_string();
}

/*******************************************************************\

Function: invariant_sett::assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::assignment(
  const exprt &lhs,
  const exprt &rhs)
{
  equal_exprt equality;
  equality.lhs()=lhs;
  equality.rhs()=rhs;
  
  // first evaluate RHS
  simplify(equality.rhs());
  ::simplify(equality.rhs(), *ns);
  
  // now kill LHS
  modifies(lhs);
  
  // and put it back
  strengthen(equality);
}

/*******************************************************************\

Function: invariant_sett::apply_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void invariant_sett::apply_code(const codet &code)
{
  const irep_idt &statement=code.get(ID_statement);

  if(statement==ID_block)
  {
    forall_operands(it, code)
      apply_code(to_code(*it));
  }
  else if(statement==ID_assign ||
          statement==ID_init)
  {
    if(code.operands().size()!=2)
      throw "assignment expected to have two operands";

    assignment(code.op0(), code.op1());
  }
  else if(statement==ID_decl)
  {
    if(code.operands().size()==2)
      assignment(code.op0(), code.op1());
    else
      modifies(code.op0());
  }
  else if(statement==ID_expression)
  {
    // this never modifies anything
  }
  else if(statement==ID_function_call)
  {
    // may be a desaster
    make_true();
  }
  else if(statement==ID_cpp_delete ||
          statement=="cpp_delete[]")
  {
    // does nothing
  }
  else if(statement==ID_free)
  {
    // does nothing
  }
  else if(statement==ID_printf)
  {
    // does nothing
  }
  else if(statement=="lock" || 
          statement=="unlock" ||
          statement==ID_asm)
  {
    // ignore for now
  }
  else
  {
    std::cerr << code.pretty() << std::endl;
    throw "invariant_sett: unexpected statement: "+id2string(statement);
  }
}
