/*******************************************************************\

Module: Invariant Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Invariant Set

#include "invariant_set.h"

#include <iostream>

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>

#include <langapi/language_util.h>

void inv_object_storet::output(std::ostream &out) const
{
  for(std::size_t i=0; i<entries.size(); i++)
    out << "STORE " << i << ": " << map[i] << '\n';
}

bool inv_object_storet::get(const exprt &expr, unsigned &n)
{
  std::string s=build_string(expr);
  if(s.empty())
    return true;

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

  if(const auto number = map.get_number(s))
  {
    n = *number;
    return false;
  }
  return true;
}

unsigned inv_object_storet::add(const exprt &expr)
{
  std::string s=build_string(expr);
  CHECK_RETURN(!s.empty());

  mapt::number_type n=map.number(s);

  if(n>=entries.size())
  {
    entries.resize(n+1);
    entries[n].expr=expr;
    entries[n].is_constant=is_constant(expr);
  }

  return n;
}

bool inv_object_storet::is_constant(unsigned n) const
{
  assert(n<entries.size());
  return entries[n].is_constant;
}

bool inv_object_storet::is_constant(const exprt &expr) const
{
  return expr.is_constant() ||
         is_constant_address(expr);
}

std::string inv_object_storet::build_string(const exprt &expr) const
{
  // we ignore some casts
  if(expr.id()==ID_typecast)
  {
    const auto &typecast_expr = to_typecast_expr(expr);

    if(
      typecast_expr.type().id() == ID_signedbv ||
      typecast_expr.type().id() == ID_unsignedbv)
    {
      const typet &op_type = typecast_expr.op().type();

      if(op_type.id() == ID_signedbv || op_type.id() == ID_unsignedbv)
      {
        if(
          to_bitvector_type(typecast_expr.type()).get_width() >=
          to_bitvector_type(op_type).get_width())
        {
          return build_string(typecast_expr.op());
        }
      }
      else if(op_type.id() == ID_bool)
      {
        return build_string(typecast_expr.op());
      }
    }
  }

  // we always track constants, but make sure they are uniquely
  // represented
  if(expr.is_constant())
  {
    // NULL?
    if(is_null_pointer(to_constant_expr(expr)))
      return "0";

    const auto i = numeric_cast<mp_integer>(expr);
    if(i.has_value())
      return integer2string(*i);
  }

  // we also like "address_of" if the object is constant
  // we don't know what mode (language) we are in, so we rely on the default
  // language to be reasonable for from_expr
  if(is_constant_address(expr))
    return from_expr(ns, irep_idt(), expr);

  if(expr.id()==ID_member)
  {
    return build_string(to_member_expr(expr).compound()) + "." +
           expr.get_string(ID_component_name);
  }

  if(expr.id()==ID_symbol)
    return id2string(to_symbol_expr(expr).get_identifier());

  return "";
}

bool invariant_sett::get_object(
  const exprt &expr,
  unsigned &n) const
{
  return object_store.get(expr, n);
}

bool inv_object_storet::is_constant_address(const exprt &expr)
{
  if(expr.id()==ID_address_of)
    return is_constant_address_rec(to_address_of_expr(expr).object());

  return false;
}

bool inv_object_storet::is_constant_address_rec(const exprt &expr)
{
  if(expr.id()==ID_symbol)
    return true;
  else if(expr.id()==ID_member)
    return is_constant_address_rec(to_member_expr(expr).compound());
  else if(expr.id()==ID_index)
  {
    const auto &index_expr = to_index_expr(expr);
    if(index_expr.index().is_constant())
      return is_constant_address_rec(index_expr.array());
  }

  return false;
}

void invariant_sett::add(
  const std::pair<unsigned, unsigned> &p,
  ineq_sett &dest)
{
  eq_set.check_index(p.first);
  eq_set.check_index(p.second);

  // add all. Quadratic.
  unsigned f_r=eq_set.find(p.first);
  unsigned s_r=eq_set.find(p.second);

  for(std::size_t f=0; f<eq_set.size(); f++)
  {
    if(eq_set.find(f)==f_r)
    {
      for(std::size_t s=0; s<eq_set.size(); s++)
        if(eq_set.find(s)==s_r)
          dest.insert(std::pair<unsigned, unsigned>(f, s));
    }
  }
}

void invariant_sett::add_eq(const std::pair<unsigned, unsigned> &p)
{
  eq_set.make_union(p.first, p.second);

  // check if there is a contradiction with two constants
  unsigned r=eq_set.find(p.first);

  bool constant_seen=false;
  mp_integer c;

  for(std::size_t i=0; i<eq_set.size(); i++)
  {
    if(eq_set.find(i)==r)
    {
      if(object_store.is_constant(i))
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
    }
  }

  // replicate <= and != constraints

  for(const auto &le : le_set)
    add_eq(le_set, p, le);

  for(const auto &ne : ne_set)
    add_eq(ne_set, p, ne);
}

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

tvt invariant_sett::is_eq(std::pair<unsigned, unsigned> p) const
{
  std::pair<unsigned, unsigned> s=p;
  std::swap(s.first, s.second);

  if(has_eq(p))
    return tvt(true);

  if(has_ne(p) || has_ne(s))
    return tvt(false);

  return tvt::unknown();
}

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

  return tvt::unknown();
}

void invariant_sett::output(std::ostream &out) const
{
  if(is_false)
  {
    out << "FALSE\n";
    return;
  }

  for(std::size_t i=0; i<eq_set.size(); i++)
    if(eq_set.is_root(i) &&
       eq_set.count(i)>=2)
    {
      bool first=true;
      for(std::size_t j=0; j<eq_set.size(); j++)
        if(eq_set.find(j)==i)
        {
          if(first)
            first=false;
          else
            out << " = ";

          out << to_string(j);
        }

      out << '\n';
    }

  for(const auto &bounds : bounds_map)
  {
    out << to_string(bounds.first) << " in " << bounds.second << '\n';
  }

  for(const auto &le : le_set)
  {
    out << to_string(le.first) << " <= " << to_string(le.second) << '\n';
  }

  for(const auto &ne : ne_set)
  {
    out << to_string(ne.first) << " != " << to_string(ne.second) << '\n';
  }
}

void invariant_sett::add_type_bounds(const exprt &expr, const typet &type)
{
  if(expr.type()==type)
    return;

  if(type.id()==ID_unsignedbv)
  {
    std::size_t op_width=to_unsignedbv_type(type).get_width();

    // TODO - 8 appears to be a magic number here -- or perhaps this should say
    // ">=" instead, and is meant to restrict types larger than a single byte?
    if(op_width<=8)
    {
      unsigned a;
      if(get_object(expr, a))
        return;

      add_bounds(a, boundst(0, power(2, op_width)-1));
    }
  }
}

void invariant_sett::strengthen(const exprt &expr)
{
  exprt tmp(expr);
  nnf(tmp);
  strengthen_rec(tmp);
}

void invariant_sett::strengthen_rec(const exprt &expr)
{
  if(expr.type().id()!=ID_bool)
    throw "non-Boolean argument to strengthen()";

  #if 0
  std::cout << "S: " << from_expr(*ns, irep_idt(), expr) << '\n';
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
  else if(expr.id()==ID_le ||
          expr.id()==ID_lt)
  {
    const auto &rel = to_binary_relation_expr(expr);

    // special rule: x <= (a & b)
    // implies:      x<=a && x<=b

    if(rel.rhs().id() == ID_bitand)
    {
      const exprt &bitand_op = rel.op1();

      forall_operands(it, bitand_op)
      {
        auto tmp(rel);
        tmp.op1()=*it;
        strengthen_rec(tmp);
      }

      return;
    }

    std::pair<unsigned, unsigned> p;

    if(get_object(rel.op0(), p.first) || get_object(rel.op1(), p.second))
      return;

    const auto i0 = numeric_cast<mp_integer>(rel.op0());
    const auto i1 = numeric_cast<mp_integer>(rel.op1());

    if(expr.id()==ID_le)
    {
      if(i0.has_value())
        add_bounds(p.second, lower_interval(*i0));
      else if(i1.has_value())
        add_bounds(p.first, upper_interval(*i1));
      else
        add_le(p);
    }
    else if(expr.id()==ID_lt)
    {
      if(i0.has_value())
        add_bounds(p.second, lower_interval(*i0 + 1));
      else if(i1.has_value())
        add_bounds(p.first, upper_interval(*i1 - 1));
      else
      {
        add_le(p);
        add_ne(p);
      }
    }
    else
      UNREACHABLE;
  }
  else if(expr.id()==ID_equal)
  {
    const auto &equal_expr = to_equal_expr(expr);

    const typet &op_type = equal_expr.op0().type();

    if(op_type.id() == ID_struct || op_type.id() == ID_struct_tag)
    {
      const struct_typet &struct_type = to_struct_type(ns.follow(op_type));

      for(const auto &comp : struct_type.components())
      {
        const member_exprt lhs_member_expr(
          equal_expr.op0(), comp.get_name(), comp.type());
        const member_exprt rhs_member_expr(
          equal_expr.op1(), comp.get_name(), comp.type());

        const equal_exprt equality(lhs_member_expr, rhs_member_expr);

        // recursive call
        strengthen_rec(equality);
      }

      return;
    }

    // special rule: x = (a & b)
    // implies:      x<=a && x<=b

    if(equal_expr.op1().id() == ID_bitand)
    {
      const exprt &bitand_op = equal_expr.op1();

      forall_operands(it, bitand_op)
      {
        auto tmp(equal_expr);
        tmp.op1()=*it;
        tmp.id(ID_le);
        strengthen_rec(tmp);
      }

      return;
    }
    else if(equal_expr.op0().id() == ID_bitand)
    {
      auto tmp(equal_expr);
      std::swap(tmp.op0(), tmp.op1());
      strengthen_rec(tmp);
      return;
    }

    // special rule: x = (type) y
    if(equal_expr.op1().id() == ID_typecast)
    {
      const auto &typecast_expr = to_typecast_expr(equal_expr.op1());
      add_type_bounds(equal_expr.op0(), typecast_expr.op().type());
    }
    else if(equal_expr.op0().id() == ID_typecast)
    {
      const auto &typecast_expr = to_typecast_expr(equal_expr.op0());
      add_type_bounds(equal_expr.op1(), typecast_expr.op().type());
    }

    std::pair<unsigned, unsigned> p, s;

    if(
      get_object(equal_expr.op0(), p.first) ||
      get_object(equal_expr.op1(), p.second))
    {
      return;
    }

    const auto i0 = numeric_cast<mp_integer>(equal_expr.op0());
    const auto i1 = numeric_cast<mp_integer>(equal_expr.op1());
    if(i0.has_value())
      add_bounds(p.second, boundst(*i0));
    else if(i1.has_value())
      add_bounds(p.first, boundst(*i1));

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
    const auto &notequal_expr = to_notequal_expr(expr);

    std::pair<unsigned, unsigned> p;

    if(
      get_object(notequal_expr.op0(), p.first) ||
      get_object(notequal_expr.op1(), p.second))
    {
      return;
    }

    // check if this is a contradiction
    if(has_eq(p))
      make_false();
    else
      add_ne(p);
  }
}

tvt invariant_sett::implies(const exprt &expr) const
{
  exprt tmp(expr);
  nnf(tmp);
  return implies_rec(tmp);
}

tvt invariant_sett::implies_rec(const exprt &expr) const
{
  if(expr.type().id()!=ID_bool)
    throw "implies: non-Boolean expression";

  #if 0
  std::cout << "I: " << from_expr(*ns, irep_idt(), expr) << '\n';
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
        return tvt::unknown();

    return tvt(true);
  }
  else if(expr.id()==ID_or)
  {
    forall_operands(it, expr)
      if(implies_rec(*it)==tvt(true))
        return tvt(true);
  }
  else if(expr.id()==ID_le ||
          expr.id()==ID_lt ||
          expr.id()==ID_equal ||
          expr.id()==ID_notequal)
  {
    const auto &rel = to_binary_relation_expr(expr);

    std::pair<unsigned, unsigned> p;

    bool ob0 = get_object(rel.lhs(), p.first);
    bool ob1 = get_object(rel.rhs(), p.second);

    if(ob0 || ob1)
      return tvt::unknown();

    tvt r;

    if(rel.id() == ID_le)
    {
      r=is_le(p);
      if(!r.is_unknown())
        return r;

      boundst b0, b1;
      get_bounds(p.first, b0);
      get_bounds(p.second, b1);

      return b0<=b1;
    }
    else if(rel.id() == ID_lt)
    {
      r=is_lt(p);
      if(!r.is_unknown())
        return r;

      boundst b0, b1;
      get_bounds(p.first, b0);
      get_bounds(p.second, b1);

      return b0<b1;
    }
    else if(rel.id() == ID_equal)
      return is_eq(p);
    else if(rel.id() == ID_notequal)
      return is_ne(p);
    else
      UNREACHABLE;
  }

  return tvt::unknown();
}

void invariant_sett::get_bounds(unsigned a, boundst &bounds) const
{
  // unbounded
  bounds=boundst();

  {
    const exprt &e_a = object_store.get_expr(a);
    const auto tmp = numeric_cast<mp_integer>(e_a);
    if(tmp.has_value())
    {
      bounds = boundst(*tmp);
      return;
    }

    if(e_a.type().id()==ID_unsignedbv)
      bounds=lower_interval(mp_integer(0));
  }

  bounds_mapt::const_iterator it=bounds_map.find(a);

  if(it!=bounds_map.end())
    bounds=it->second;
}

void invariant_sett::nnf(exprt &expr, bool negate)
{
  if(expr.type().id()!=ID_bool)
    throw "nnf: non-Boolean expression";

  if(expr.is_true())
  {
    if(negate)
      expr=false_exprt();
  }
  else if(expr.is_false())
  {
    if(negate)
      expr=true_exprt();
  }
  else if(expr.id()==ID_not)
  {
    nnf(to_not_expr(expr).op(), !negate);
    exprt tmp;
    tmp.swap(to_not_expr(expr).op());
    expr.swap(tmp);
  }
  else if(expr.id()==ID_and)
  {
    if(negate)
      expr.id(ID_or);

    Forall_operands(it, expr)
      nnf(*it, negate);
  }
  else if(expr.id()==ID_or)
  {
    if(negate)
      expr.id(ID_and);

    Forall_operands(it, expr)
      nnf(*it, negate);
  }
  else if(expr.id()==ID_typecast)
  {
    const auto &typecast_expr = to_typecast_expr(expr);

    if(
      typecast_expr.op().type().id() == ID_unsignedbv ||
      typecast_expr.op().type().id() == ID_signedbv)
    {
      equal_exprt tmp(
        typecast_expr.op(), from_integer(0, typecast_expr.op().type()));
      nnf(tmp, !negate);
      expr.swap(tmp);
    }
    else if(negate)
    {
      expr = boolean_negate(expr);
    }
  }
  else if(expr.id()==ID_le)
  {
    if(negate)
    {
      // !a<=b <-> !b=>a <-> b<a
      expr.id(ID_lt);
      auto &rel = to_binary_relation_expr(expr);
      std::swap(rel.lhs(), rel.rhs());
    }
  }
  else if(expr.id()==ID_lt)
  {
    if(negate)
    {
      // !a<b <-> !b>a <-> b<=a
      expr.id(ID_le);
      auto &rel = to_binary_relation_expr(expr);
      std::swap(rel.lhs(), rel.rhs());
    }
  }
  else if(expr.id()==ID_ge)
  {
    if(negate)
      expr.id(ID_lt);
    else
    {
      expr.id(ID_le);
      auto &rel = to_binary_relation_expr(expr);
      std::swap(rel.lhs(), rel.rhs());
    }
  }
  else if(expr.id()==ID_gt)
  {
    if(negate)
      expr.id(ID_le);
    else
    {
      expr.id(ID_lt);
      auto &rel = to_binary_relation_expr(expr);
      std::swap(rel.lhs(), rel.rhs());
    }
  }
  else if(expr.id()==ID_equal)
  {
    if(negate)
      expr.id(ID_notequal);
  }
  else if(expr.id()==ID_notequal)
  {
    if(negate)
      expr.id(ID_equal);
  }
  else if(negate)
  {
    expr = boolean_negate(expr);
  }
}

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
    for(std::size_t i=0; i<eq_set.size(); i++)
      if(eq_set.find(i)==r)
      {
        const exprt &e = object_store.get_expr(i);

        if(e.is_constant())
        {
          const mp_integer value =
            numeric_cast_v<mp_integer>(to_constant_expr(e));

          if(expr.type().id()==ID_pointer)
          {
            if(value==0)
              return null_pointer_exprt(to_pointer_type(expr.type()));
          }
          else
            return from_integer(value, expr.type());
        }
        else if(object_store.is_constant_address(e))
        {
          if(e.type()==expr.type())
            return e;

          return typecast_exprt(e, expr.type());
        }
      }
  }

  return static_cast<const exprt &>(get_nil_irep());
}

std::string inv_object_storet::to_string(unsigned a) const
{
  return id2string(map[a]);
}

std::string invariant_sett::to_string(unsigned a) const
{
  return object_store.to_string(a);
}

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
  std::size_t old_ne_set=ne_set.size();
  std::size_t old_le_set=le_set.size();

  intersection(ne_set, other.ne_set);
  intersection(le_set, other.le_set);

  // bounds
  if(make_union_bounds_map(other.bounds_map))
    return true;

  if(old_eq_roots!=eq_set.count_roots() ||
     old_ne_set!=ne_set.size() ||
     old_le_set!=le_set.size())
    return true;

  return false; // no change
}

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
      if(it->second!=old)
        changed=true;
      it++;
    }
  }

  return changed;
}

void invariant_sett::modifies(unsigned a)
{
  eq_set.isolate(a);
  remove(ne_set, a);
  remove(le_set, a);
  bounds_map.erase(a);
}

void invariant_sett::modifies(const exprt &lhs)
{
  if(lhs.id()==ID_symbol ||
     lhs.id()==ID_member)
  {
    unsigned a;
    if(!get_object(lhs, a))
      modifies(a);
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
    modifies(to_if_expr(lhs).op1());
    modifies(to_if_expr(lhs).op2());
  }
  else if(lhs.id()==ID_typecast)
  {
    // just go down
    modifies(to_typecast_expr(lhs).op());
  }
  else if(lhs.id()=="valid_object")
  {
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    // just go down
    modifies(to_byte_extract_expr(lhs).op0());
  }
  else if(lhs.id() == ID_null_object ||
          lhs.id() == "is_zero_string" ||
          lhs.id() == "zero_string" ||
          lhs.id() == "zero_string_length")
  {
    // ignore
  }
  else
    throw "modifies: unexpected lhs: "+lhs.id_string();
}

void invariant_sett::assignment(
  const exprt &lhs,
  const exprt &rhs)
{
  equal_exprt equality(lhs, rhs);

  // first evaluate RHS
  simplify(equality.rhs());
  ::simplify(equality.rhs(), ns);

  // now kill LHS
  modifies(lhs);

  // and put it back
  strengthen(equality);
}

void invariant_sett::apply_code(const codet &code)
{
  const irep_idt &statement=code.get(ID_statement);

  if(statement==ID_block)
  {
    forall_operands(it, code)
      apply_code(to_code(*it));
  }
  else if(statement==ID_assign)
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
    // may be a disaster
    make_true();
  }
  else if(statement==ID_cpp_delete ||
          statement==ID_cpp_delete_array)
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
    std::cerr << code.pretty() << '\n';
    throw "invariant_sett: unexpected statement: "+id2string(statement);
  }
}
