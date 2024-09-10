/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "std_expr.h"

#include "arith_tools.h"
#include "config.h"
#include "expr_util.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include "mathematical_types.h"
#include "namespace.h"
#include "pointer_expr.h"
#include "range.h"
#include "rational.h"
#include "rational_tools.h"
#include "substitute_symbols.h"

#include <map>

constant_exprt::constant_exprt(bool value)
  : constant_exprt(value ? ID_true : ID_false, bool_typet{})
{
}

bool constant_exprt::value_is_zero_string() const
{
  const std::string val=id2string(get_value());
  return val.find_first_not_of('0')==std::string::npos;
}

bool constant_exprt::is_true() const
{
  return is_boolean() && get_value() != ID_false;
}

bool constant_exprt::is_false() const
{
  return is_boolean() && get_value() == ID_false;
}

bool constant_exprt::is_zero() const
{
  const irep_idt &type_id = type().id();

  if(type_id == ID_integer)
  {
    return integer_typet{}.zero_expr() == *this;
  }
  else if(type_id == ID_natural)
  {
    return natural_typet{}.zero_expr() == *this;
  }
  else if(type_id == ID_real)
  {
    return real_typet{}.zero_expr() == *this;
  }
  else if(type_id == ID_rational)
  {
    rationalt rat_value;
    if(to_rational(*this, rat_value))
      CHECK_RETURN(false);
    return rat_value.is_zero();
  }
  else if(
    type_id == ID_unsignedbv || type_id == ID_signedbv ||
    type_id == ID_c_bool || type_id == ID_c_bit_field)
  {
    return value_is_zero_string();
  }
  else if(type_id == ID_fixedbv)
  {
    return fixedbvt(*this).is_zero();
  }
  else if(type_id == ID_floatbv)
  {
    return ieee_floatt(*this).is_zero();
  }
  else if(type_id == ID_pointer)
  {
    return is_null_pointer();
  }
  else
    return false;
}

bool constant_exprt::is_one() const
{
  const irep_idt &type_id = type().id();

  if(type_id == ID_integer)
  {
    return integer_typet{}.one_expr() == *this;
  }
  else if(type_id == ID_natural)
  {
    return natural_typet{}.one_expr() == *this;
  }
  else if(type_id == ID_real)
  {
    return real_typet{}.one_expr() == *this;
  }
  else if(type_id == ID_rational)
  {
    rationalt rat_value;
    if(to_rational(*this, rat_value))
      CHECK_RETURN(false);
    return rat_value.is_one();
  }
  else if(
    type_id == ID_unsignedbv || type_id == ID_signedbv ||
    type_id == ID_c_bool || type_id == ID_c_bit_field)
  {
    const auto width = to_bitvector_type(type()).get_width();
    mp_integer int_value = bvrep2integer(id2string(get_value()), width, false);
    return int_value == 1;
  }
  else if(type_id == ID_fixedbv)
  {
    fixedbv_spect spec{to_fixedbv_type(type())};
    fixedbvt one{spec};
    one.from_integer(1);
    return one == fixedbvt{*this};
  }
  else if(type_id == ID_floatbv)
  {
    ieee_floatt one{to_floatbv_type(type())};
    one.from_integer(1);
    return one == ieee_floatt{*this};
  }
  else
    return false;
}

bool constant_exprt::is_null_pointer() const
{
  if(type().id() != ID_pointer)
    return false;

  if(get_value() == ID_NULL)
    return true;

    // We used to support "0" (when NULL_is_zero), but really front-ends should
    // resolve this and generate ID_NULL instead.
#if 0
  return config.ansi_c.NULL_is_zero && value_is_zero_string();
#else
  INVARIANT(
    !value_is_zero_string() || !config.ansi_c.NULL_is_zero,
    "front-end should use ID_NULL");
  return false;
#endif
}

void constant_exprt::check(const exprt &expr, const validation_modet vm)
{
  nullary_exprt::check(expr, vm);

  const auto value = expr.get(ID_value);

  DATA_CHECK(
    vm,
    !can_cast_type<bitvector_typet>(expr.type()) || !value.empty(),
    "bitvector constant must have a non-empty value");

  DATA_CHECK(
    vm,
    !can_cast_type<bitvector_typet>(expr.type()) ||
      can_cast_type<pointer_typet>(expr.type()) ||
      expr.type().id() == ID_verilog_unsignedbv ||
      expr.type().id() == ID_verilog_signedbv ||
      id2string(value).find_first_not_of("0123456789ABCDEF") ==
        std::string::npos,
    "negative bitvector constant must use two's complement");

  DATA_CHECK(
    vm,
    !can_cast_type<bitvector_typet>(expr.type()) ||
      expr.type().id() == ID_verilog_unsignedbv ||
      expr.type().id() == ID_verilog_signedbv || value == ID_0 ||
      id2string(value)[0] != '0',
    "bitvector constant must not have leading zeros");
}

exprt disjunction(const exprt::operandst &op)
{
  if(op.empty())
    return false_exprt();
  else if(op.size()==1)
    return op.front();
  else
  {
    return or_exprt(exprt::operandst(op));
  }
}

exprt conjunction(exprt a, exprt b)
{
  PRECONDITION(a.is_boolean() && b.is_boolean());
  if(b.is_constant())
  {
    if(to_constant_expr(b).is_false())
      return false_exprt{};
    return a;
  }
  if(a.is_constant())
  {
    if(to_constant_expr(a).is_false())
      return false_exprt{};
    return b;
  }
  if(b.id() == ID_and)
  {
    b.add_to_operands(std::move(a));
    return b;
  }
  return and_exprt{std::move(a), std::move(b)};
}

exprt conjunction(const exprt::operandst &op)
{
  if(op.empty())
    return true_exprt();
  else if(op.size()==1)
    return op.front();
  else if(op.size() == 2)
    return conjunction(op[0], op[1]);
  else
  {
    return and_exprt(exprt::operandst(op));
  }
}

// Implementation of struct_exprt::component for const / non const overloads.
template <typename T>
auto component(T &struct_expr, const irep_idt &name, const namespacet &ns)
  -> decltype(struct_expr.op0())
{
  static_assert(
    std::is_base_of<struct_exprt, T>::value, "T must be a struct_exprt.");
  const struct_typet &struct_type =
    struct_expr.type().id() == ID_struct_tag
      ? ns.follow_tag(to_struct_tag_type(struct_expr.type()))
      : to_struct_type(struct_expr.type());
  const auto index = struct_type.component_number(name);
  DATA_INVARIANT(
    index < struct_expr.operands().size(),
    "component matching index should exist");
  return struct_expr.operands()[index];
}

/// \return The expression for a named component of this struct.
exprt &struct_exprt::component(const irep_idt &name, const namespacet &ns)
{
  return ::component(*this, name, ns);
}

/// \return The expression for a named component of this struct.
const exprt &
struct_exprt::component(const irep_idt &name, const namespacet &ns) const
{
  return ::component(*this, name, ns);
}

/// Check that the member expression has the right number of operands, refers
/// to a component that exists on its underlying compound type, and uses the
/// same type as is declared on that compound type. Throws or raises an
/// invariant if not, according to validation mode.
/// \param expr: expression to validate
/// \param ns: global namespace
/// \param vm: validation mode (see \ref exprt::validate)
void member_exprt::validate(
  const exprt &expr,
  const namespacet &ns,
  const validation_modet vm)
{
  check(expr, vm);

  const auto &member_expr = to_member_expr(expr);

  const typet &compound_type = member_expr.compound().type();
  const auto *struct_union_type =
    (compound_type.id() == ID_struct_tag || compound_type.id() == ID_union_tag)
      ? &ns.follow_tag(to_struct_or_union_tag_type(compound_type))
      : type_try_dynamic_cast<struct_union_typet>(compound_type);
  DATA_CHECK(
    vm,
    struct_union_type != nullptr,
    "member must address a struct, union or compatible type");

  const auto &component =
    struct_union_type->get_component(member_expr.get_component_name());

  DATA_CHECK(
    vm,
    component.is_not_nil(),
    "member component '" + id2string(member_expr.get_component_name()) +
      "' must exist on addressed type");

  DATA_CHECK(
    vm,
    component.type() == member_expr.type(),
    "member expression's type must match the addressed struct or union "
    "component");
}

void let_exprt::validate(const exprt &expr, const validation_modet vm)
{
  check(expr, vm);

  const auto &let_expr = to_let_expr(expr);

  DATA_CHECK(
    vm,
    let_expr.values().size() == let_expr.variables().size(),
    "number of variables must match number of values");

  for(const auto &binding :
      make_range(let_expr.variables()).zip(let_expr.values()))
  {
    DATA_CHECK(
      vm,
      binding.first.id() == ID_symbol,
      "let binding symbols must be symbols");

    DATA_CHECK(
      vm,
      binding.first.type() == binding.second.type(),
      "let bindings must be type consistent");
  }
}

with_exprt update_exprt::make_with_expr() const
{
  const exprt::operandst &designators = designator();
  PRECONDITION(!designators.empty());

  with_exprt result{exprt{}, exprt{}, exprt{}};
  exprt *dest = &result;

  for(const auto &expr : designators)
  {
    with_exprt tmp{exprt{}, exprt{}, exprt{}};

    if(expr.id() == ID_index_designator)
    {
      tmp.where() = to_index_designator(expr).index();
    }
    else if(expr.id() == ID_member_designator)
    {
      // irep_idt component_name=
      //  to_member_designator(*it).get_component_name();
    }
    else
      UNREACHABLE;

    *dest = tmp;
    dest = &to_with_expr(*dest).new_value();
  }

  return result;
}

exprt binding_exprt::instantiate(const operandst &values) const
{
  // number of values must match the number of bound variables
  auto &variables = this->variables();
  PRECONDITION(variables.size() == values.size());

  std::map<symbol_exprt, exprt> value_map;

  for(std::size_t i = 0; i < variables.size(); i++)
  {
    // types must match
    PRECONDITION(variables[i].type() == values[i].type());
    value_map[variables[i]] = values[i];
  }

  // build a substitution map
  std::map<irep_idt, exprt> substitutions;

  for(std::size_t i = 0; i < variables.size(); i++)
    substitutions[variables[i].get_identifier()] = values[i];

  // now recurse downwards and substitute in 'where'
  auto substitute_result = substitute_symbols(substitutions, where());

  if(substitute_result.has_value())
    return substitute_result.value();
  else
    return where(); // trivial case, variables not used
}

exprt binding_exprt::instantiate(const variablest &new_variables) const
{
  std::vector<exprt> values;
  values.reserve(new_variables.size());
  for(const auto &new_variable : new_variables)
    values.push_back(new_variable);
  return instantiate(values);
}
