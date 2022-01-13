/*******************************************************************\

Module: Base Type Computation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Base Type Computation

#include "base_type.h"

#include <set>

#include "namespace.h"
#include "pointer_expr.h"
#include "symbol.h"
#include "union_find.h"

class base_type_eqt
{
public:
  explicit base_type_eqt(const namespacet &_ns):ns(_ns)
  {
  }

  bool base_type_eq(const typet &type1, const typet &type2)
  {
    identifiers.clear();
    return base_type_eq_rec(type1, type2);
  }

  bool base_type_eq(const exprt &expr1, const exprt &expr2)
  {
    identifiers.clear();
    return base_type_eq_rec(expr1, expr2);
  }

  virtual ~base_type_eqt() { }

protected:
  const namespacet &ns;

  virtual bool base_type_eq_rec(const typet &type1, const typet &type2);
  virtual bool base_type_eq_rec(const exprt &expr1, const exprt &expr2);

  // for loop avoidance
  typedef union_find<irep_idt> identifierst;
  identifierst identifiers;
};

void base_type_rec(
  typet &type, const namespacet &ns, std::set<irep_idt> &symb)
{
  if(
    type.id() == ID_c_enum_tag || type.id() == ID_struct_tag ||
    type.id() == ID_union_tag)
  {
    const symbolt *symbol;

    if(
      !ns.lookup(to_tag_type(type).get_identifier(), symbol) &&
      symbol->is_type && !symbol->type.is_nil())
    {
      type=symbol->type;
      base_type_rec(type, ns, symb); // recursive call
      return;
    }
  }
  else if(type.id()==ID_array)
  {
    base_type_rec(to_array_type(type).subtype(), ns, symb);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    struct_union_typet::componentst &components=
      to_struct_union_type(type).components();

    for(auto &component : components)
      base_type_rec(component.type(), ns, symb);
  }
  else if(type.id()==ID_pointer)
  {
    typet &base_type = to_pointer_type(type).base_type();

    // we need to avoid running into an infinite loop
    if(
      base_type.id() == ID_c_enum_tag || base_type.id() == ID_struct_tag ||
      base_type.id() == ID_union_tag)
    {
      const irep_idt &id = to_tag_type(base_type).get_identifier();

      if(symb.find(id)!=symb.end())
        return;

      symb.insert(id);

      base_type_rec(base_type, ns, symb);

      symb.erase(id);
    }
    else
      base_type_rec(base_type, ns, symb);
  }
}

void base_type(typet &type, const namespacet &ns)
{
  std::set<irep_idt> symb;
  base_type_rec(type, ns, symb);
}

void base_type(exprt &expr, const namespacet &ns)
{
  base_type(expr.type(), ns);

  Forall_operands(it, expr)
    base_type(*it, ns);
}

bool base_type_eqt::base_type_eq_rec(
  const typet &type1,
  const typet &type2)
{
  if(type1==type2)
    return true;

  #if 0
  std::cout << "T1: " << type1.pretty() << '\n';
  std::cout << "T2: " << type2.pretty() << '\n';
  #endif

  // loop avoidance
  if(
    (type1.id() == ID_c_enum_tag || type1.id() == ID_struct_tag ||
     type1.id() == ID_union_tag) &&
    type2.id() == type1.id())
  {
    // already in same set?
    if(identifiers.make_union(
         type1.get(ID_identifier),
         type2.get(ID_identifier)))
      return true;
  }

  if(
    type1.id() == ID_c_enum_tag || type1.id() == ID_struct_tag ||
    type1.id() == ID_union_tag)
  {
    const symbolt &symbol=
      ns.lookup(type1.get(ID_identifier));

    if(!symbol.is_type)
      return false;

    return base_type_eq_rec(symbol.type, type2);
  }

  if(
    type2.id() == ID_c_enum_tag || type2.id() == ID_struct_tag ||
    type2.id() == ID_union_tag)
  {
    const symbolt &symbol=
      ns.lookup(type2.get(ID_identifier));

    if(!symbol.is_type)
      return false;

    return base_type_eq_rec(type1, symbol.type);
  }

  if(type1.id()!=type2.id())
    return false;

  if(type1.id()==ID_struct ||
     type1.id()==ID_union)
  {
    const struct_union_typet::componentst &components1=
      to_struct_union_type(type1).components();

    const struct_union_typet::componentst &components2=
      to_struct_union_type(type2).components();

    if(components1.size()!=components2.size())
      return false;

    for(std::size_t i=0; i<components1.size(); i++)
    {
      const typet &subtype1=components1[i].type();
      const typet &subtype2=components2[i].type();
      if(!base_type_eq_rec(subtype1, subtype2))
        return false;
      if(components1[i].get_name()!=components2[i].get_name())
        return false;
    }

    return true;
  }
  else if(type1.id()==ID_code)
  {
    const code_typet::parameterst &parameters1=
      to_code_type(type1).parameters();

    const code_typet::parameterst &parameters2=
      to_code_type(type2).parameters();

    if(parameters1.size()!=parameters2.size())
      return false;

    for(std::size_t i=0; i<parameters1.size(); i++)
    {
      const typet &subtype1=parameters1[i].type();
      const typet &subtype2=parameters2[i].type();
      if(!base_type_eq_rec(subtype1, subtype2))
        return false;
    }

    const typet &return_type1=to_code_type(type1).return_type();
    const typet &return_type2=to_code_type(type2).return_type();

    if(!base_type_eq_rec(return_type1, return_type2))
      return false;

    return true;
  }
  else if(type1.id()==ID_pointer)
  {
    return base_type_eq_rec(
      to_pointer_type(type1).base_type(), to_pointer_type(type2).base_type());
  }
  else if(type1.id()==ID_array)
  {
    if(!base_type_eq_rec(
      to_array_type(type1).subtype(), to_array_type(type2).subtype()))
      return false;

    if(to_array_type(type1).size()!=to_array_type(type2).size())
      return false;

    return true;
  }

  // the below will go away
  typet tmp1(type1), tmp2(type2);

  base_type(tmp1, ns);
  base_type(tmp2, ns);

  return tmp1==tmp2;
}

bool base_type_eqt::base_type_eq_rec(
  const exprt &expr1,
  const exprt &expr2)
{
  if(expr1.id()!=expr2.id())
    return false;

  if(!base_type_eq(expr1.type(), expr2.type()))
    return false;

  const exprt::operandst &expr1_op=expr1.operands();
  const exprt::operandst &expr2_op=expr2.operands();
  if(expr1_op.size()!=expr2_op.size())
    return false;

  for(exprt::operandst::const_iterator
      it1=expr1_op.begin(), it2=expr2_op.begin();
      it1!=expr1_op.end() && it2!=expr2_op.end();
      ++it1, ++it2)
    if(!base_type_eq(*it1, *it2))
      return false;

  if(expr1.id()==ID_constant)
    if(expr1.get(ID_value)!=expr2.get(ID_value))
      return false;

  return true;
}

/// Check types for equality across all levels of hierarchy.
/// Example:
/// - `struct_typet {union_tag_typet("a")}` and `struct_typet {ns.lookup("a")
///   .type}` will compare equal.
/// \param type1: The first type to compare.
/// \param type2: The second type to compare.
/// \param ns: The namespace, needed for resolution of symbols.
bool base_type_eq(
  const typet &type1,
  const typet &type2,
  const namespacet &ns)
{
  base_type_eqt base_type_eq(ns);
  return base_type_eq.base_type_eq(type1, type2);
}

/// Check expressions for equality across all levels of hierarchy.
/// \param expr1: The first expression to compare.
/// \param expr2: The second expression to compare.
/// \param ns: The namespace, needed for resolution of symbols.
bool base_type_eq(
  const exprt &expr1,
  const exprt &expr2,
  const namespacet &ns)
{
  base_type_eqt base_type_eq(ns);
  return base_type_eq.base_type_eq(expr1, expr2);
}
