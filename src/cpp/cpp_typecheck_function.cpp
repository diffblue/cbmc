/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_convert_type.h"
#include "cpp_name.h"
#include "cpp_sfinae_context.h"
#include "cpp_template_type.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"

#include <functional>
#include <optional>
#include <set>

void cpp_typecheckt::convert_parameter(
  const irep_idt &current_mode,
  code_typet::parametert &parameter)
{
  irep_idt base_name=id2string(parameter.get_base_name());

  if(base_name.empty())
  {
    base_name="#anon_arg"+std::to_string(anon_counter++);
    parameter.set_base_name(base_name);
  }

  PRECONDITION(!cpp_scopes.current_scope().prefix.empty());
  irep_idt identifier=cpp_scopes.current_scope().prefix+
                      id2string(base_name);

  parameter.set_identifier(identifier);

  // the parameter may already have been set up if dealing with virtual methods
  const symbolt *check_symbol;
  if(!lookup(identifier, check_symbol))
    return;

  parameter_symbolt symbol;

  symbol.name=identifier;
  symbol.base_name=parameter.get_base_name();
  symbol.location=parameter.source_location();
  symbol.mode = current_mode;
  symbol.module=module;
  symbol.type=parameter.type();
  symbol.is_lvalue=!is_reference(symbol.type);

  INVARIANT(!symbol.base_name.empty(), "parameter has base name");

  symbolt *new_symbol;

  if(symbol_table.move(symbol, new_symbol))
  {
    error().source_location=symbol.location;
    error() << "cpp_typecheckt::convert_parameter: symbol_table.move("
            << quote_begin << symbol.name << quote_end << ") failed" << eom;
    throw 0;
  }

  // put into scope
  cpp_scopes.put_into_scope(*new_symbol);
}

void cpp_typecheckt::convert_parameters(
  const irep_idt &current_mode,
  code_typet &function_type)
{
  code_typet::parameterst &parameters=
    function_type.parameters();

  for(code_typet::parameterst::iterator
      it=parameters.begin();
      it!=parameters.end();
      it++)
    convert_parameter(current_mode, *it);
}

/// N5008 [dcl.type.auto.deduct]: placeholder type deduction.  \p declared is
/// the type T containing the placeholder, \p initializer the (type-checked)
/// initializer-clause E, \p parenthesized whether E was written as a
/// parenthesized id-expression or member access (see decltype_of).  Returns
/// the type T' that replaces T.
///
/// * `decltype(auto)` ([dcl.type.auto.deduct]/4): T is the placeholder alone
///   and T' is decltype(E).
/// * `auto` ([dcl.type.auto.deduct]/3): T' is obtained as by template argument
///   deduction from a function call with P = T (the placeholder standing for
///   the invented parameter U) and argument E ([temp.deduct.call]/2-3): when P
///   is not a reference, an array A decays to a pointer, a function A to a
///   function pointer, and A's top-level cv-qualifiers are ignored; when P is
///   a reference, the referred type of P is used and A keeps its qualifiers
///   (`const auto &r = ci` is `const int &`); a forwarding reference (`auto
///   &&`) with an lvalue E deduces an lvalue reference.  The placeholder is
///   then substituted through P's ptr-operators (`auto *p = <T*>` gives
///   U = T).
typet cpp_typecheckt::deduce_placeholder_type(
  const typet &declared,
  const exprt &initializer,
  bool parenthesized)
{
  PRECONDITION(has_auto(declared));

  if(declared.id() == ID_decltype && declared.get_bool("#auto"))
  {
    typet deduced = decltype_of(initializer, parenthesized);
    typecheck_type(deduced);
    return deduced;
  }

  typet pattern = declared;

  // A is the type of E.  An expression never has reference type; the front
  // end marks a glvalue produced through a reference with the reference type
  // itself, so the referred type is the one deduction sees.
  typet argument = cpp_bool_type(initializer.type());
  if(argument.id() == ID_c_bit_field)
    argument = to_c_bit_field_type(argument).underlying_type();
  if(is_reference(argument) || is_rvalue_reference(argument))
    argument = to_pointer_type(argument).base_type();

  const bool pattern_is_reference =
    is_reference(pattern) || is_rvalue_reference(pattern);

  // A function designator arrives already converted to its address (an
  // implicit address_of).  For a reference pattern [temp.deduct.call]/2.2
  // does not apply: A is the function type, so `auto &f = fn' deduces a
  // reference to function -- deducing a pointer made the binding fail ("bad
  // reference initializer"; CBMC's own goto-harness, `auto &f =
  // harness_options_parser::require_exactly_one_value', dog-fooding).
  if(
    pattern_is_reference && initializer.id() == ID_address_of &&
    initializer.get_bool(ID_C_implicit) &&
    to_address_of_expr(initializer).object().type().id() == ID_code)
  {
    argument = to_address_of_expr(initializer).object().type();
  }

  if(!pattern_is_reference)
  {
    // [temp.deduct.call]/2
    if(argument.id() == ID_array)
      argument = pointer_type(to_array_type(argument).element_type());
    else if(argument.id() == ID_code)
      argument = pointer_type(argument);
    argument.remove(ID_C_constant);
    argument.remove(ID_C_volatile);
  }
  else if(
    is_rvalue_reference(pattern) &&
    to_pointer_type(pattern).base_type().id() == ID_auto &&
    !to_pointer_type(pattern).base_type().get_bool(ID_C_constant) &&
    !to_pointer_type(pattern).base_type().get_bool(ID_C_volatile) &&
    is_lvalue_expression(initializer))
  {
    // [temp.deduct.call]/3: a forwarding reference bound to an lvalue
    // deduces U as an lvalue reference; with reference collapsing
    // ([dcl.ref]/6) the declared `auto &&` is then an lvalue reference.
    pattern.remove(ID_C_rvalue_reference);
  }

  cpp_convert_auto(pattern, argument, get_message_handler());
  typecheck_type(pattern);
  return pattern;
}

/// N5008 [dcl.type.auto.deduct]/2.1 and [dcl.spec.auto.general]/10-13: the
/// return type of a function declared with a placeholder is deduced from each
/// non-discarded return statement.  The first deduction fixes the type (it is
/// usable in the rest of the body, /13); every later return statement must
/// deduce the same type (/10).  The operand is then converted to the deduced
/// type as for any return statement ([stmt.return]/2).
void cpp_typecheckt::deduce_return_type(code_frontend_returnt &code)
{
  const typet &declared = declared_return_type;
  PRECONDITION(has_auto(declared));

  const bool placeholder_alone =
    declared.id() == ID_auto ||
    (declared.id() == ID_decltype && declared.get_bool("#auto"));

  typet deduced;

  if(!code.has_return_value())
  {
    // [dcl.type.auto.deduct]/2.1.1: E is void(); T shall be the placeholder
    // alone (`auto *g() { }` is ill-formed, [dcl.spec.auto.general]/11)
    if(!placeholder_alone)
    {
      error().source_location = code.source_location();
      error() << "cannot deduce '" << to_string(declared) << "' from void()"
              << eom;
      throw 0;
    }
    deduced = void_type();
  }
  else
  {
    // read before type-checking rebuilds the node
    const bool parenthesized = code.return_value().get_bool(ID_C_parenthesized);

    typecheck_expr(code.return_value());

    // N5008 [dcl.spec.auto.general]/11: an expression naming a function
    // whose placeholder return type is still undeduced is ill-formed; here
    // that happens when the callee's body could not be type-checked (and
    // was dropped), so no type can be deduced from the operand either.
    // Fail this function's deduction rather than leave the placeholder in
    // the operand's type.
    if(
      code.return_value().type().id() == ID_decltype ||
      has_auto(code.return_value().type()))
    {
      error().source_location = code.source_location();
      error() << "cannot deduce the return type from an operand of undeduced "
              << "type '" << to_string(code.return_value().type()) << "'"
              << eom;
      throw 0;
    }

    if(code.return_value().id() == ID_initializer_list)
    {
      // [dcl.type.auto.deduct]/2.1.2
      error().source_location = code.source_location();
      error() << "cannot deduce a return type from a braced-init-list" << eom;
      throw 0;
    }

    if(code.return_value().type().id() == ID_empty && !placeholder_alone)
    {
      error().source_location = code.source_location();
      error() << "cannot deduce '" << to_string(declared) << "' from an "
              << "expression of type void" << eom;
      throw 0;
    }

    deduced =
      deduce_placeholder_type(declared, code.return_value(), parenthesized);
  }

  if(!has_auto(return_type))
  {
    // a previous return statement deduced the type already
    if(deduced != return_type)
    {
      error().source_location = code.source_location();
      error() << "inconsistent deduction for the return type: '"
              << to_string(return_type) << "' and '" << to_string(deduced)
              << "'" << eom;
      throw 0;
    }
  }
  else
  {
    return_type = deduced;
    if(deducing_function_type != nullptr)
      deducing_function_type->return_type() = deduced;
  }

  if(code.has_return_value() && return_type.id() != ID_empty)
  {
    if(is_reference(return_type) || is_rvalue_reference(return_type))
      reference_initializer(
        code.return_value(), to_reference_type(return_type));
    else
      implicit_typecast(code.return_value(), return_type);
  }
}

cpp_typecheckt::return_deduction_contextt::return_deduction_contextt(
  cpp_typecheckt &_typecheck,
  code_typet &_function_type,
  bool deduce)
  : typecheck(_typecheck),
    function_type(_function_type),
    saved_return_type(_typecheck.return_type),
    saved_declared_return_type(_typecheck.declared_return_type),
    saved_deducing_function_type(_typecheck.deducing_function_type)
{
  if(deduce)
  {
    typecheck.return_type = typet(ID_auto);
    typecheck.deducing_function_type = &function_type;
  }
  else
  {
    typecheck.return_type = function_type.return_type();
    typecheck.deducing_function_type = nullptr;
  }
  typecheck.declared_return_type = typecheck.return_type;
}

cpp_typecheckt::return_deduction_contextt::~return_deduction_contextt()
{
  typecheck.return_type = saved_return_type;
  typecheck.declared_return_type = saved_declared_return_type;
  typecheck.deducing_function_type = saved_deducing_function_type;
}

void cpp_typecheckt::return_deduction_contextt::finish()
{
  if(!has_auto(typecheck.declared_return_type))
    return;
  // [dcl.spec.auto.general]/11 -- a lambda's placeholder is `auto' alone
  function_type.return_type() = has_auto(typecheck.return_type)
                                  ? typet(void_type())
                                  : typecheck.return_type;
}

/// N5008 [class.spaceship]/2-4, [class.compare.default]/6: the body of a
/// defaulted three-way comparison: the elements of the expanded lists of
/// subobjects (direct bases, then non-static data members, arrays element by
/// element) are compared in order, and the first result that is not equal is
/// returned, converted to the return type R; otherwise R(equal).  For a
/// declared `auto', R is the common comparison type of the element results.
/// \return the body (and \p function_type's return type set to R), or
///   nothing if a comparison cannot be formed this way (the caller then uses
///   its simpler lowering)
/// [cmp.categories]: a comparison category converts to a weaker one by its
/// conversion function (strong_ordering to weak_ordering / partial_ordering,
/// weak_ordering to partial_ordering).  \return whether \p value (of a
/// comparison category type) was converted to \p category into \p result
bool cpp_typecheckt::convert_to_comparison_category(
  const exprt &value,
  const typet &category,
  exprt &result)
{
  typet value_type = value.type();
  value_type.remove(ID_C_constant);
  typet target = category;
  target.remove(ID_C_constant);
  if(value_type == target)
  {
    result = value;
    return true;
  }
  if(value_type.id() != ID_struct_tag || target.id() != ID_struct_tag)
    return false;
  // the conversion function `operator R() const' of the value's class
  const struct_typet &value_class = follow_tag(to_struct_tag_type(value_type));
  for(const auto &c : value_class.components())
  {
    if(c.type().id() != ID_code || c.get_bool(ID_is_static))
      continue;
    const code_typet &code_type = to_code_type(c.type());
    typet return_type = code_type.return_type();
    return_type.remove(ID_C_constant);
    if(
      return_type != target || code_type.parameters().size() != 1 ||
      id2string(c.get_base_name()).rfind("operator", 0) != 0)
    {
      continue;
    }
    const symbolt *function = symbol_table.lookup(c.get_name());
    if(function == nullptr)
      continue;
    exprt object = value;
    if(!object.get_bool(ID_C_lvalue))
    {
      // a temporary holding the prvalue, for the `this' argument
      side_effect_exprt temporary{
        ID_temporary_object, value_type, value.source_location()};
      temporary.set(ID_mode, ID_cpp);
      temporary.add_to_operands(value);
      object = std::move(temporary);
    }
    side_effect_expr_function_callt call{
      function->symbol_expr(),
      {typecast_exprt::conditional_cast(
        address_of_exprt{object}, code_type.parameters().front().type())},
      code_type.return_type(),
      value.source_location()};
    result = std::move(call);
    return true;
  }
  return false;
}

/// N5008 [class.compare.default]/6: the expanded list of subobjects of the
/// operands of the defaulted comparison \p symbol: its direct base class
/// subobjects, then its non-static data members, an array element by
/// element, as pairs of lvalues of the two operands.
/// \return false if the list cannot be formed (a virtual base, a reference
///   member)
bool cpp_typecheckt::defaulted_comparison_elements(
  const symbolt &symbol,
  code_typet &function_type,
  const exprt &this_expr,
  std::vector<std::pair<exprt, exprt>> &elements)
{
  const auto &parameters = function_type.parameters();
  irep_idt class_id = symbol.type.get(ID_C_member_name);
  const bool is_friend = class_id.empty();
  if(is_friend)
    class_id = symbol.type.get(ID_C_class);
  if(class_id.empty())
    return false;
  // a member has the parameters (this, y), a friend (x, y)
  if(parameters.size() != 2)
    return false;
  const symbolt &class_symbol = lookup(class_id);
  if(class_symbol.type.id() != ID_struct)
    return false;
  const struct_typet &class_type = to_struct_type(class_symbol.type);

  // the operands x and y, as lvalues of the class type
  const auto parameter_object = [&](const code_typet::parametert &p) -> exprt
  {
    const symbol_exprt param{p.get_identifier(), p.type()};
    exprt object;
    if(p.type().id() == ID_pointer)
      object = dereference_exprt{param, to_pointer_type(p.type()).base_type()};
    else
      object = param;
    object.set(ID_C_lvalue, true);
    return object;
  };
  exprt x, y;
  if(is_friend)
  {
    x = parameter_object(parameters[0]);
    y = parameter_object(parameters[1]);
  }
  else
  {
    if(this_expr.is_nil())
      return false;
    x = dereference_exprt{
      this_expr, to_pointer_type(this_expr.type()).base_type()};
    x.set(ID_C_lvalue, true);
    y = parameter_object(parameters[1]);
  }

  // the expanded lists of subobjects ([class.compare.default]/6)
  for(const auto &base : class_type.bases())
  {
    if(base.get_bool(ID_virtual))
      return false;
    exprt bx = address_of_exprt{x};
    exprt by = address_of_exprt{y};
    typet base_type = base.type();
    pointer_typet bx_type = pointer_type(base_type);
    bx_type.base_type().set(ID_C_constant, x.type().get_bool(ID_C_constant));
    pointer_typet by_type = pointer_type(base_type);
    by_type.base_type().set(ID_C_constant, true);
    make_ptr_typecast(bx, bx_type, false, true);
    make_ptr_typecast(by, by_type, false, true);
    exprt ex = dereference_exprt{bx, bx_type.base_type()};
    exprt ey = dereference_exprt{by, by_type.base_type()};
    ex.set(ID_C_lvalue, true);
    ey.set(ID_C_lvalue, true);
    elements.emplace_back(ex, ey);
  }
  std::function<void(const exprt &, const exprt &)> add_element =
    [&](const exprt &ex, const exprt &ey)
  {
    if(ex.type().id() == ID_array)
    {
      const auto size =
        numeric_cast<mp_integer>(to_array_type(ex.type()).size());
      for(mp_integer i = 0; size.has_value() && i < *size; ++i)
      {
        const exprt index = from_integer(i, c_index_type());
        exprt ix = index_exprt{ex, index};
        exprt iy = index_exprt{ey, index};
        ix.set(ID_C_lvalue, true);
        iy.set(ID_C_lvalue, true);
        add_element(ix, iy);
      }
      return;
    }
    elements.emplace_back(ex, ey);
  };
  for(const auto &c : class_type.components())
  {
    if(
      c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
      c.get_bool(ID_is_static) || c.get_is_padding() ||
      c.type().id() == ID_code || c.get_bool(ID_is_vtptr))
    {
      continue;
    }
    if(is_reference(c.type()))
      return false; // [class.compare.default]/2: deleted
    exprt mx = member_exprt{x, c.get_name(), c.type()};
    exprt my = member_exprt{y, c.get_name(), c.type()};
    mx.set(ID_C_lvalue, true);
    my.set(ID_C_lvalue, true);
    add_element(mx, my);
  }

  return true;
}

std::optional<code_blockt> cpp_typecheckt::defaulted_three_way_comparison(
  const symbolt &symbol,
  code_typet &function_type,
  const exprt &this_expr)
{
  std::vector<std::pair<exprt, exprt>> elements;
  if(!defaulted_comparison_elements(symbol, function_type, this_expr, elements))
    return {};
  const source_locationt &location = symbol.location;

  // the element comparisons xi <=> yi
  std::vector<exprt> comparisons;
  const std::size_t errors_before =
    get_message_handler().get_message_count(messaget::M_ERROR);
  try
  {
    for(const auto &element : elements)
    {
      exprt comparison{ID_spaceship};
      comparison.add_to_operands(
        already_typechecked_exprt{element.first},
        already_typechecked_exprt{element.second});
      comparison.add_source_location() = location;
      typecheck_expr(comparison);
      comparisons.push_back(std::move(comparison));
    }
  }
  catch(...)
  {
    get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
    return {};
  }

  // R: declared, or the common comparison type ([class.spaceship]/4)
  const auto category_of = [](const typet &t) -> int
  {
    if(t.id() != ID_struct_tag)
      return -1;
    const std::string id = id2string(to_struct_tag_type(t).get_identifier());
    if(id.find("tag-partial_ordering") != std::string::npos)
      return 0;
    if(id.find("tag-weak_ordering") != std::string::npos)
      return 1;
    if(id.find("tag-strong_ordering") != std::string::npos)
      return 2;
    return -1;
  };
  typet result_type = function_type.return_type();
  if(has_auto(result_type))
  {
    int common = 2;
    std::optional<typet> chosen;
    for(const auto &comparison : comparisons)
    {
      typet t = comparison.type();
      t.remove(ID_C_constant);
      const int category = category_of(t);
      if(category < 0)
        return {};
      if(category <= common || !chosen.has_value())
      {
        if(!chosen.has_value() || category < common)
          chosen = t;
        common = std::min(common, category);
      }
    }
    if(!chosen.has_value())
    {
      // no elements: strong_ordering, the type of a strong comparison
      exprt zero_cmp{ID_spaceship};
      zero_cmp.add_to_operands(
        from_integer(0, signed_int_type()), from_integer(0, signed_int_type()));
      zero_cmp.add_source_location() = location;
      typecheck_expr(zero_cmp);
      chosen = zero_cmp.type();
      chosen->remove(ID_C_constant);
      if(category_of(*chosen) != 2)
        return {};
    }
    result_type = *chosen;
    function_type.return_type() = result_type;
  }
  if(category_of(result_type) < 0)
    return {};

  code_blockt body;
  body.add_source_location() = location;
  try
  {
    for(auto &comparison : comparisons)
    {
      // [class.spaceship]/1.1: static_cast<R>(xi <=> yi)
      exprt value;
      if(!convert_to_comparison_category(comparison, result_type, value))
        throw 0;
      // `value != 0' ([cmp.categories.pre]/3: compared with a literal 0)
      exprt test{ID_notequal};
      test.add_to_operands(
        already_typechecked_exprt{value}, from_integer(0, signed_int_type()));
      test.add_source_location() = location;
      typecheck_expr(test);
      code_frontend_returnt ret{already_typechecked_exprt{value}};
      ret.add_source_location() = location;
      code_ifthenelset branch{
        already_typechecked_exprt{std::move(test)}, std::move(ret)};
      branch.add_source_location() = location;
      body.add(std::move(branch));
    }
    // static_cast<R>(std::strong_ordering::equal), i.e. R's equal value:
    // the result of `0 <=> 0' converted to R
    exprt equal{ID_spaceship};
    equal.add_to_operands(
      from_integer(0, signed_int_type()), from_integer(0, signed_int_type()));
    equal.add_source_location() = location;
    typecheck_expr(equal);
    exprt equal_value;
    if(!convert_to_comparison_category(equal, result_type, equal_value))
      throw 0;
    equal = std::move(equal_value);
    code_frontend_returnt ret{already_typechecked_exprt{equal}};
    ret.add_source_location() = location;
    body.add(std::move(ret));
  }
  catch(...)
  {
    get_message_handler().set_message_count(messaget::M_ERROR, errors_before);
    return {};
  }
  return body;
}

void cpp_typecheckt::convert_function(symbolt &symbol)
{
  // N5008 [class.access.general]/4 + [class.default.ctor]/4: the body of
  // an implicitly-defined constructor/destructor, or one explicitly
  // defaulted on its first declaration ([dcl.fct.def.default]/5), is a
  // member of its class, so its member initializations may name that
  // class's own private members.  Record the class for the access check; an
  // EXACT-match context is used deliberately, because a base class's
  // private members remain inaccessible there (regression/cpp/
  // Protection1: `class B : A {}` with A's private default constructor
  // must still be rejected).
  struct implicit_definition_guardt
  {
    irep_idt &slot;
    const irep_idt saved;
    implicit_definition_guardt(irep_idt &s, const irep_idt &v)
      : slot(s), saved(s)
    {
      if(!v.empty())
        slot = v;
    }
    ~implicit_definition_guardt()
    {
      slot = saved;
    }
  } implicit_definition_guard{
    implicit_definition_class,
    (symbol.type.get_bool("#is_implicit_ctor") ||
     symbol.type.get_bool("#is_implicit_dtor") ||
     symbol.type.get_bool("#explicitly_defaulted"))
      ? symbol.type.get(ID_C_member_name)
      : irep_idt{}};
  // Guard against recursive type-checking (e.g., constexpr functions
  // that call themselves).
  if(functions_being_typechecked.count(symbol.name))
    return;

  // Idempotence: a body that completed conversion carries
  // #cpp_converted (set at the end of this function).  The
  // method-bodies drain warns that convert must never run twice for
  // one symbol, but eager call-site conversions (auto-return
  // deduction, callee-body preparation) and the drain can both reach
  // the same instance; the second run re-typechecks the
  // already-typechecked body, which does not re-typecheck cleanly
  // (materialised references, resolved calls -- e.g. re-binding a
  // forwarded xvalue fails, N5008 [forward]/4 + [dcl.init.ref]/5.3).
  if(symbol.value.get_bool("#cpp_converted"))
    return;

  // Released on every exit path -- an early return, or a failure thrown out
  // of the body conversion.  A name left behind made every later attempt to
  // convert the body (the method-body drain, after a first try inside a
  // SFINAE guard had failed silently) return at the recursion guard above,
  // and the function silently ended up without a body.
  struct being_typecheckedt
  {
    being_typecheckedt(std::unordered_set<irep_idt> &set, const irep_idt &name)
      : set(set), name(name)
    {
      set.insert(name);
    }
    ~being_typecheckedt()
    {
      set.erase(name);
    }
    std::unordered_set<irep_idt> &set;
    irep_idt name;
  } being_typechecked{functions_being_typechecked, symbol.name};

  // A function body is a run-time context: suspend any enclosing
  // constant-expression context so its statements are not folded.
  non_constant_expression_contextt non_constant_guard{*this};

  // for the deleted-implicit-member recovery below
  const std::size_t errors_before_conversion =
    get_message_handler().get_message_count(messaget::M_ERROR);

  code_typet &function_type=
    to_code_type(template_subtype(symbol.type));

  // only a prototype?
  if(symbol.value.is_nil())
    return;

  // the parsed body as it arrived, for the retry below (irept is shared, so
  // this copy is cheap)
  const exprt original_body = symbol.value;

  if(symbol.value.id() != ID_code)
  {
    error().source_location = symbol.location;
    error() << "function '" << symbol.name << "' is initialized with "
            << symbol.value.id() << eom;
    throw 0;
  }

  // C++11 deleted functions: = delete
  if(to_code(symbol.value).get_statement() == ID_cpp_delete)
  {
    symbol.value.make_nil();
    return;
  }

  // N5008 [temp.variadic]/5 + [dcl.spec.auto]/11: a function-template instance
  // whose body contains a call-argument pack expansion over a NON-type
  // parameter pack (e.g. `return add(I...)`) is normally expanded during the
  // deferred method-body drain (which runs expand_call_argument_packs).  A
  // function with a DEDUCED return type (`auto` / `decltype(auto)`) is instead
  // type-checked EAGERLY here, so its return type is known at the call site;
  // that path bypasses the drain, so without expanding the pack call first both
  // the return-type deduction and the body type-check below fail on the
  // unexpanded `add(I...)` (leaving the instance's return type unresolved, so
  // the call "finds no match").  Expand it now using this instance's deduced
  // pack values.  Gated on both a deduced return type and a non-type pack being
  // present (pack_expr_map), so the working deferred path and bodies with only
  // type / function-parameter packs are untouched; the expansion is idempotent
  // (an already-expanded call carries no `...`), so a later drain is a no-op.
  //
  // only_nontype: this eager conversion may run while an ENCLOSING
  // instantiation's template_map is still active (a nested deduced-return
  // callee -- e.g. std::apply's __apply_impl deducing its return type from
  // std::__invoke(...), which is itself instantiated here).  A function-
  // parameter pack in THIS body was already expanded at instantiation time, so
  // only the non-type call-argument pack must be expanded; expanding a value /
  // function-parameter pack against the enclosing map's unrelated pack size
  // would corrupt an already-expanded call (`add(a$0, a$1)` -> `add(a$0,
  // a$0)`).
  //
  // The same applies to a `constexpr` function-template instance reached from
  // a constant-expression context (is_macro), which cpp_declarator_convertert
  // converts eagerly for the same reason, and to a TYPE parameter pack of two
  // or more elements: `{__is_same(_Tp, _Types)...}` in libstdc++'s
  // __find_uniq_type_in_pack (std::variant's __exactly_once) otherwise
  // resolves the pack name to its first element only and the braced list
  // collapses to one element.
  //
  // Likewise an EMPTY pack ([temp.variadic]/7): libc++'s `constexpr auto
  // __get_comp_type()' builds `{_StrongOrd, __type_to_enum<_Ts>()...}' and
  // is constant-evaluated for common_comparison_category_t<>.
  bool has_multi_element_type_pack = false;
  for(const auto &pa : template_map.pack_args_map)
    if(pa.second.size() >= 2)
      has_multi_element_type_pack = true;
  bool has_empty_pack = false;
  for(const auto &ps : template_map.pack_size_map)
    if(ps.second == 0)
      has_empty_pack = true;
  if(
    (has_auto(symbol.type) || symbol.is_macro) &&
    (!template_map.pack_expr_map.empty() || has_multi_element_type_pack ||
     has_empty_pack))
  {
    template_map.expand_call_argument_packs(
      static_cast<irept &>(symbol.value), /*only_nontype=*/true);
  }

  // enter appropriate scope
  cpp_save_scopet saved_scope(cpp_scopes);
  cpp_scopet &function_scope=cpp_scopes.set_scope(symbol.name);

  // fix the scope's prefix
  function_scope.prefix=id2string(symbol.name)+"::";

  // For friend functions defined inside a class, add the class scope
  // as a secondary scope so that class-scope names are visible.  Access
  // is NOT disabled: N5008 [class.friend]/1 lets a friend name the
  // befriending class's private and protected members, which
  // check_component_access grants; a friend of B gets no access to a
  // class D that merely derives from B privately ([class.access.base]/4).
  const irep_idt &friend_class = symbol.type.get(ID_C_class);
  bool saved_access_control = disable_access_control;
  if(!friend_class.empty())
  {
    auto it = cpp_scopes.id_map.find(friend_class);
    if(it != cpp_scopes.id_map.end())
      function_scope.add_secondary_scope(
        static_cast<cpp_scopet &>(*it->second));
  }

  // genuine function definition -- do the parameter declarations
  // N5008 [dcl.fct.def.general]/2: the type of a parameter or the return
  // type of a function DEFINITION shall not be an incomplete class type;
  // [temp.inst]/2 instantiates the class template specializations named
  // there (naming them in a declaration did not, [temp.inst]/1).
  for(auto &parameter : function_type.parameters())
    elaborate_class_template(parameter.type());
  elaborate_class_template(function_type.return_type());
  convert_parameters(symbol.mode, function_type);

  // create "this" if it's a non-static method
  if(function_scope.is_method &&
     !function_scope.is_static_member)
  {
    code_typet::parameterst &parameters=function_type.parameters();
    DATA_INVARIANT(parameters.size() >= 1, "parameters expected");
    code_typet::parametert &this_parameter_expr=parameters.front();
    function_scope.this_expr = symbol_exprt{
      this_parameter_expr.get_identifier(), this_parameter_expr.type()};
  }
  else
    function_scope.this_expr.make_nil();

  // if it is a destructor, add the implicit code
  if(to_code_type(symbol.type).return_type().id() == ID_destructor)
  {
    const symbolt &msymb = lookup(symbol.type.get(ID_C_member_name));

    // Under normal operation a destructor body arrives here as a
    // code_blockt.  However, under error-recovery conditions (for
    // example after a prior CONVERSION ERROR has produced a
    // partially-elaborated class) we may see a destructor symbol
    // whose value is nil or not a block.  Skip the implicit-code
    // insertion in that case rather than aborting via a
    // PRECONDITION violation.
    if(
      symbol.value.id() != ID_code ||
      symbol.value.get(ID_statement) != ID_block)
    {
      return;
    }

    // Skip adding destructor code for virtual function thunks — the
    // thunk just calls the real destructor which already has the code.
    const auto &this_param_type =
      to_pointer_type(function_type.parameters().front().type());
    bool is_thunk =
      this_param_type.base_type().get(ID_identifier) != msymb.name;

    if(
      !is_thunk &&
      (!symbol.value.has_operands() ||
       !to_multi_ary_expr(symbol.value).op0().has_operands() ||
       to_multi_ary_expr(to_multi_ary_expr(symbol.value).op0()).op0().id() !=
         ID_already_typechecked))
    {
      codet prologue = code_skipt();
      codet epilogue =
        dtor(msymb, to_symbol_expr(function_scope.this_expr), prologue);
      symbol.value.copy_to_operands(epilogue);
      if(prologue.get_statement() != ID_skip)
      {
        exprt::operandst &statements = symbol.value.operands();
        statements.insert(statements.begin(), prologue);
      }
    }
  }

  // do the function body
  // Save and restore the return type and loop-context flags
  // exception-safely.  convert_function may be called recursively (e.g. a
  // template instantiation triggered while type-checking an expression in
  // another function body).  If such a nested call throws and is caught
  // upstream, a non-exception-safe restore would leave `return_type` set to
  // the nested function's return type; the enclosing function's subsequent
  // `return` statements would then be converted against the wrong type
  // (N5008 [stmt.return]/3 requires the operand to be implicitly converted
  // to the *enclosing* function's return type).  That produces a
  // type-inconsistent assignment that later trips the symbolic-execution
  // invariant lhs.type() == rhs.type().  A scope guard restores the saved
  // values on every exit -- normal return, early return, or exception.
  struct context_restoret
  {
    typet &return_type_ref;
    typet &declared_return_type_ref;
    code_typet *&deducing_function_type_ref;
    bool &break_ref;
    bool &continue_ref;
    bool &case_ref;
    const typet saved_return_type;
    const typet saved_declared_return_type;
    code_typet *const saved_deducing_function_type;
    const bool saved_break;
    const bool saved_continue;
    const bool saved_case;
    ~context_restoret()
    {
      return_type_ref = saved_return_type;
      declared_return_type_ref = saved_declared_return_type;
      deducing_function_type_ref = saved_deducing_function_type;
      break_ref = saved_break;
      continue_ref = saved_continue;
      case_ref = saved_case;
    }
  } context_restore{
    return_type,
    declared_return_type,
    deducing_function_type,
    break_is_allowed,
    continue_is_allowed,
    case_is_allowed,
    return_type,
    declared_return_type,
    deducing_function_type,
    break_is_allowed,
    continue_is_allowed,
    case_is_allowed};

  start_typecheck_code();

  return_type = function_type.return_type();

  // constructor, destructor?
  if(return_type.id() == ID_constructor || return_type.id() == ID_destructor)
    return_type = void_type();

  // N5008 [dcl.spec.auto.general]/4, /13: a placeholder return type is
  // deduced from the non-discarded return statements as the body is
  // type-checked (typecheck_return -> deduce_return_type); the first
  // deduction is written into the function type at once so the rest of the
  // body (a recursive call) sees it.  `return_type' is the running
  // deduction, `declared_return_type' the T of [dcl.type.auto.deduct]/2.1.
  declared_return_type = return_type;
  deducing_function_type = has_auto(return_type) ? &function_type : nullptr;

  // C++20: generate body for defaulted operator<=>
  if(
    symbol.base_name == "operator<=>" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    auto body = defaulted_three_way_comparison(
      symbol, function_type, function_scope.this_expr);
    if(body.has_value())
    {
      symbol.value = std::move(*body);
      return_type = function_type.return_type();
      declared_return_type = return_type;
      deducing_function_type = nullptr;
    }
  }
  if(
    symbol.base_name == "operator<=>" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    const irep_idt &class_id = symbol.type.get(ID_C_member_name);
    if(!class_id.empty())
    {
      const symbolt &class_sym = lookup(class_id);
      const auto &fn_params = to_code_type(symbol.type).parameters();
      // Find the parameter name (second param after this)
      irep_idt arg_name;
      if(fn_params.size() >= 2)
        arg_name = fn_params[1].get_base_name();
      if(arg_name.empty())
        arg_name = "#anon_arg0";

      source_locationt loc = symbol.location;
      code_blockt body;
      body.add_source_location() = loc;

      for(const auto &c : to_struct_type(class_sym.type).components())
      {
        // N5008 [class.compare.default]/6, [class.eq]/2: the expanded list
        // of subobjects is the base classes and the non-static data
        // MEMBERS; padding inserted by the layout is neither and has no
        // name (comparing it yielded "symbol '' is unknown" for every class
        // whose members are not tightly packed, `char *ptr; errc ec;').
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.get_is_padding() ||
          c.type().id() == ID_code)
          continue;

        const irep_idt &mem = c.get_base_name();
        cpp_namet lhs(mem, loc);
        exprt rhs(ID_member);
        rhs.add(ID_component_cpp_name, cpp_namet(mem, loc));
        rhs.copy_to_operands(cpp_namet(arg_name, loc).as_expr());
        rhs.add_source_location() = loc;

        typet int_type = signed_int_type();
        binary_relation_exprt lt(lhs.as_expr(), ID_lt, rhs);
        lt.add_source_location() = loc;
        binary_relation_exprt gt(lhs.as_expr(), ID_gt, rhs);
        gt.add_source_location() = loc;
        if_exprt inner(
          std::move(gt), from_integer(1, int_type), from_integer(0, int_type));
        inner.add_source_location() = loc;
        if_exprt cmp(
          std::move(lt), from_integer(-1, int_type), std::move(inner));
        cmp.add_source_location() = loc;

        notequal_exprt ne(cmp, from_integer(0, int_type));
        ne.add_source_location() = loc;
        code_frontend_returnt ret(cmp);
        ret.add_source_location() = loc;
        code_ifthenelset ifs(std::move(ne), std::move(ret));
        ifs.add_source_location() = loc;
        body.add(std::move(ifs));
      }

      code_frontend_returnt ret0(from_integer(0, signed_int_type()));
      ret0.add_source_location() = loc;
      body.add(std::move(ret0));

      symbol.value = std::move(body);
    }
  }

  // N5008 [class.eq]/2-3: a defaulted operator== compares the elements of
  // the expanded lists of subobjects -- bases, members, array elements --
  // with ==, in order, and yields false at the first that is not equal
  if(
    symbol.base_name == "operator==" && symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    std::vector<std::pair<exprt, exprt>> elements;
    const std::size_t errors_before =
      get_message_handler().get_message_count(messaget::M_ERROR);
    if(defaulted_comparison_elements(
         symbol, function_type, function_scope.this_expr, elements))
    {
      try
      {
        exprt result = true_exprt{};
        for(const auto &element : elements)
        {
          exprt eq{ID_equal};
          eq.add_to_operands(
            already_typechecked_exprt{element.first},
            already_typechecked_exprt{element.second});
          eq.add_source_location() = symbol.location;
          typecheck_expr(eq);
          implicit_typecast_bool(eq);
          result = result.is_true() ? eq : and_exprt{result, eq};
        }
        code_blockt body;
        body.add_source_location() = symbol.location;
        code_frontend_returnt ret{already_typechecked_exprt{result}};
        ret.add_source_location() = symbol.location;
        body.add(std::move(ret));
        symbol.value = std::move(body);
      }
      catch(...)
      {
        get_message_handler().set_message_count(
          messaget::M_ERROR, errors_before);
      }
    }
  }

  // N5008 [class.compare.default]/1: a defaulted `operator==' or
  // `operator!=' is either a non-static const member with one parameter of
  // type `const C &' or a friend with two such parameters.  [class.eq]/2:
  // the defaulted == returns the conjunction of the memberwise comparisons
  // of the expanded list of subobjects ([class.compare.default]/6, the
  // non-static data members in declaration order); [class.compare.default]
  // /1 + [over.match.oper]: a defaulted != is `!(x == y)`.  Both forms are
  // elaborated here from the empty `= default' body.
  if(
    (symbol.base_name == "operator==" || symbol.base_name == "operator!=") &&
    symbol.value.id() == ID_code &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands())
  {
    irep_idt class_id = symbol.type.get(ID_C_member_name);
    // For the friend form, the befriending class
    if(class_id.empty())
      class_id = symbol.type.get(ID_C_class);
    if(!class_id.empty())
    {
      const symbolt &class_sym = lookup(class_id);
      const auto &fn_params = to_code_type(symbol.type).parameters();
      const bool is_friend_op = symbol.type.get(ID_C_member_name).empty();
      irep_idt lhs_name, rhs_name;
      if(is_friend_op && fn_params.size() >= 2)
      {
        lhs_name = fn_params[0].get_base_name();
        rhs_name = fn_params[1].get_base_name();
      }
      else if(fn_params.size() >= 2)
      {
        rhs_name = fn_params[1].get_base_name();
      }
      if(is_friend_op && lhs_name.empty())
        lhs_name = "#anon_arg0";
      if(rhs_name.empty())
        rhs_name = "#anon_arg1";

      source_locationt loc = symbol.location;

      // Build conjunction: m1==rhs.m1 && m2==rhs.m2 && ...
      exprt result = true_exprt();
      for(const auto &c : to_struct_type(class_sym.type).components())
      {
        // N5008 [class.compare.default]/6, [class.eq]/2: the expanded list
        // of subobjects is the base classes and the non-static data
        // MEMBERS; padding inserted by the layout is neither and has no
        // name (comparing it yielded "symbol '' is unknown" for every class
        // whose members are not tightly packed, `char *ptr; errc ec;').
        if(
          c.get_bool(ID_from_base) || c.get_bool(ID_is_type) ||
          c.get_bool(ID_is_static) || c.get_is_padding() ||
          c.type().id() == ID_code)
          continue;

        const irep_idt &mem = c.get_base_name();
        exprt lhs_expr;
        if(is_friend_op)
        {
          lhs_expr = exprt(ID_member);
          lhs_expr.add(ID_component_cpp_name, cpp_namet(mem, loc));
          lhs_expr.copy_to_operands(cpp_namet(lhs_name, loc).as_expr());
          lhs_expr.add_source_location() = loc;
        }
        else
        {
          lhs_expr = cpp_namet(mem, loc).as_expr();
        }
        exprt rhs_expr(ID_member);
        rhs_expr.add(ID_component_cpp_name, cpp_namet(mem, loc));
        rhs_expr.copy_to_operands(cpp_namet(rhs_name, loc).as_expr());
        rhs_expr.add_source_location() = loc;

        equal_exprt eq(std::move(lhs_expr), std::move(rhs_expr));
        eq.add_source_location() = loc;

        if(result.is_true())
          result = std::move(eq);
        else
        {
          and_exprt conj(std::move(result), std::move(eq));
          conj.add_source_location() = loc;
          result = std::move(conj);
        }
      }

      if(symbol.base_name == "operator!=")
      {
        not_exprt neg(std::move(result));
        neg.add_source_location() = loc;
        result = std::move(neg);
      }

      code_blockt body;
      body.add_source_location() = loc;
      code_frontend_returnt ret(std::move(result));
      ret.add_source_location() = loc;
      body.add(std::move(ret));

      symbol.value = std::move(body);
    }
  }

  // [dcl.fct.def.default], [class.copy.ctor]/14: an explicitly-defaulted
  // copy or move constructor memberwise copies/moves the base subobjects and
  // non-static data members.  Generate those initializers here, at
  // conversion time: the class is fully formed (so base/member types are
  // known) and this only runs for constructors actually being elaborated,
  // avoiding eager instantiation pressure during class type-checking (which
  // could otherwise perturb overload resolution in heavy system headers).
  // The body was marked "#defaulted_function" and its sole reference
  // parameter named "ref" when the `= default` definition was type-checked.
  if(
    symbol.value.id() == ID_code &&
    symbol.value.get_bool("#defaulted_function") &&
    to_code(symbol.value).get_statement() == ID_block &&
    to_code_type(symbol.type).return_type().id() == ID_constructor)
  {
    const code_typet &ft = to_code_type(symbol.type);
    const irep_idt class_id = symbol.type.get(ID_C_member_name);
    // implicit this + exactly one reference parameter whose referent is the
    // constructor's own class == the copy/move constructor.  Both the copy
    // constructor (lvalue reference, T&) and the move constructor (rvalue
    // reference, T&&) are handled: for the trivially-copyable members we
    // restrict to below, a memberwise move is a memberwise copy
    // ([class.copy.ctor]/15 -- scalar and pointer members are simply copied),
    // so the same generated body is correct for either.
    if(ft.parameters().size() == 2 && !class_id.empty())
    {
      const typet &pt = ft.parameters()[1].type();
      const bool is_ref_to_self =
        pt.id() == ID_pointer &&
        (pt.get_bool(ID_C_reference) || pt.get_bool(ID_C_rvalue_reference)) &&
        to_pointer_type(pt).base_type().id() == ID_struct_tag &&
        to_struct_tag_type(to_pointer_type(pt).base_type()).get_identifier() ==
          class_id;
      const symbolt *class_symbol = symbol_table.lookup(class_id);
      bool has_virtual_base = false;
      if(class_symbol != nullptr && class_symbol->type.id() == ID_struct)
      {
        // Virtual bases require most-derived construction order
        // ([class.base.init]/7,13); CBMC's virtual-base member handling is
        // independently incomplete, so leave such (rare) defaulted ctors
        // with an empty body rather than emitting unsound copies.
        std::list<irep_idt> vbases;
        get_virtual_bases(to_struct_type(class_symbol->type), vbases);
        has_virtual_base = !vbases.empty();
      }
      // Only generate the memberwise copy/move when every base subobject and
      // non-static data member is trivially copyable: a scalar, an array of
      // such, an empty class, or (recursively) a class all of whose own data
      // members are trivially copyable.  A defaulted copy/move constructor is
      // well-formed irrespective of the class's *other* user-declared
      // constructors, so we deliberately do not gate on cpp_is_pod (which
      // rejects e.g. std::_Rb_tree_iterator merely for having a user-provided
      // converting constructor); we look only at the data members' types.
      // For such members a memberwise move coincides with a memberwise copy
      // ([class.copy.ctor]/15), so default_cpctor's copy initializers are
      // correct for the move constructor too.  A class with a union member
      // (e.g. std::basic_string's small-string buffer) is excluded, which
      // also keeps us away from unmodelled library copies such as
      // std::string's _S_copy_chars / _M_replace.
      bool all_members_trivial = true;
      if(class_symbol != nullptr && class_symbol->type.id() == ID_struct)
      {
        std::set<irep_idt> visiting;
        std::function<bool(const typet &)> is_trivial_copy =
          [&](const typet &t) -> bool
        {
          typet et = t;
          while(et.id() == ID_array)
            et = to_array_type(et).element_type();
          if(
            et.id() == ID_pointer || et.id() == ID_signedbv ||
            et.id() == ID_unsignedbv || et.id() == ID_floatbv ||
            et.id() == ID_fixedbv || et.id() == ID_c_bool ||
            et.id() == ID_bool || et.id() == ID_c_enum ||
            et.id() == ID_c_enum_tag)
            return true;
          if(et.id() == ID_struct_tag)
          {
            const irep_idt tag = to_struct_tag_type(et).get_identifier();
            const symbolt *s = symbol_table.lookup(tag);
            if(s == nullptr || s->type.id() != ID_struct)
              return s != nullptr && cpp_is_pod(s->type);
            // Guard against (pathological) recursive containment.
            if(!visiting.insert(tag).second)
              return true;
            bool ok = true;
            for(const auto &mc : to_struct_type(s->type).components())
            {
              if(
                mc.get_bool(ID_is_static) || mc.get_bool(ID_is_type) ||
                mc.type().id() == ID_code || mc.get_bool(ID_is_vtptr))
                continue;
              if(!is_trivial_copy(mc.type()))
                ok = false;
            }
            visiting.erase(tag);
            return ok;
          }
          return false;
        };
        const struct_typet &st = to_struct_type(class_symbol->type);
        for(const auto &b : st.bases())
          if(!is_trivial_copy(b.type()))
            all_members_trivial = false;
        for(const auto &c : st.components())
        {
          if(
            c.get_bool(ID_is_static) || c.get_bool(ID_is_type) ||
            c.type().id() == ID_code || c.get_bool(ID_from_base) ||
            c.get_bool(ID_is_vtptr))
            continue;
          if(!is_trivial_copy(c.type()))
            all_members_trivial = false;
        }
      }
      // N5008 [class.copy.ctor]/14: an explicitly-defaulted copy/move
      // constructor performs a memberwise copy/move.  The skeleton's
      // per-base/member DEFAULT initializers are tolerable for members
      // the trivial fast path below overwrites -- but when a BASE or
      // MEMBER has a DELETED (ID_noaccess) or no default constructor,
      // the skeleton is guaranteed ill-formed where the defaulted copy
      // is NOT (`goto_symex_statet(const&) = default` deriving from
      // goto_statet with `goto_statet() = delete`; CBMC's own
      // goto-symex sources).  Generate the memberwise copy for that
      // case as well.
      bool skeleton_needs_deleted_default = false;
      if(class_symbol != nullptr && class_symbol->type.id() == ID_struct)
      {
        auto default_ctor_deleted = [&](const typet &t) -> bool
        {
          if(t.id() != ID_struct_tag)
            return false;
          const symbolt *ts =
            symbol_table.lookup(to_struct_tag_type(t).get_identifier());
          if(ts == nullptr || ts->type.id() != ID_struct)
            return false;
          bool has_any_ctor = false;
          for(const auto &comp : to_struct_type(ts->type).components())
          {
            if(
              comp.type().id() != ID_code ||
              to_code_type(comp.type()).return_type().id() != ID_constructor)
              continue;
            has_any_ctor = true;
            if(to_code_type(comp.type()).parameters().size() == 1)
              return comp.get(ID_access) == ID_noaccess;
          }
          // constructors exist but no default constructor at all
          return has_any_ctor;
        };
        for(const auto &b : to_struct_type(class_symbol->type).bases())
        {
          if(default_ctor_deleted(b.type()))
          {
            skeleton_needs_deleted_default = true;
            break;
          }
        }
        if(!skeleton_needs_deleted_default)
        {
          for(const auto &comp :
              to_struct_type(class_symbol->type).components())
          {
            if(
              comp.get_bool(ID_from_base) || comp.get_bool(ID_is_type) ||
              comp.get_bool(ID_is_static) || comp.get_is_padding() ||
              comp.type().id() == ID_code)
              continue;
            if(default_ctor_deleted(comp.type()))
            {
              skeleton_needs_deleted_default = true;
              break;
            }
          }
        }
      }
      // N5008 [dcl.fct.def.default]/5 + [class.copy.ctor]/14-15: an
      // explicitly-defaulted copy/move constructor that is not deleted is
      // defined exactly as the implicit one -- a memberwise copy/move of
      // the bases and members -- whatever the members' types.  This used
      // to be generated only when every member was trivially copyable
      // (all_members_trivial, computed above and kept for the diagnostic
      // record): for any other class the body stayed EMPTY, so the members
      // were default-initialised instead of copied.  `std::pair<int,
      // std::function<int()>>`'s defaulted copy constructor produced an
      // empty std::function (the call operator reached
      // __throw_bad_function_call), and every class holding such a member
      // with `T(const T &) = default;` copied nothing.
      (void)all_members_trivial;
      if(is_ref_to_self && class_symbol != nullptr && !has_virtual_base)
      {
        // default_cpctor emits initializers that refer to the source
        // object by the parameter name "ref".  Make "ref" resolve to this
        // constructor's actual parameter for the duration of body
        // type-checking by aliasing it in the function scope.  (Done here,
        // not by renaming the parameter at class-typecheck time, so that
        // class elaboration / overload resolution is left untouched.)
        cpp_idt &ref_id = function_scope.insert(irep_idt{"ref"});
        ref_id.identifier = ft.parameters()[1].get_identifier();
        ref_id.id_class = cpp_idt::id_classt::SYMBOL;
        ref_id.is_member = false;

        cpp_declarationt tmp_cpctor;
        default_cpctor(
          *class_symbol, tmp_cpctor, "ref", pt.get_bool(ID_C_rvalue_reference));
        const irept &inits = tmp_cpctor.declarators()[0].member_initializers();
        // The defaulted constructor's body, at this point, consists solely of
        // the member initializers that move_member_initializers inserted from
        // the (empty) `= default` member-initializer list: for every base and
        // non-static data member, a *default* initializer.  Replacing them
        // wholesale with default_cpctor's memberwise *copy* initializers turns
        // the body into the implicit copy/move constructor
        // ([class.copy.ctor]/14): a default initializer left in place would
        // run after the copy and overwrite it (this is why a plain prepend was
        // not enough for class-typed members, which -- unlike scalars -- do
        // get a default member initializer).
        auto &ops = symbol.value.operands();
        ops.clear();
        for(const auto &init : inits.get_sub())
          ops.push_back(static_cast<const exprt &>(init));
      }
    }
  }

  // [dcl.fct.def.default] + [class.copy.assign]/12-13: an explicitly-defaulted
  // copy/move assignment operator performs memberwise assignment of the base
  // subobjects and non-static data members (the source cast to an xvalue for
  // the move operator, so base/member *move* assignment operators are
  // selected).  Elaborate the body here, at conversion time, exactly like the
  // defaulted copy/move constructor above; without this the `= default` body
  // stays an empty block and the operator silently returns nondet.
  if(
    symbol.value.id() == ID_code &&
    symbol.value.get_bool("#defaulted_function") &&
    to_code(symbol.value).get_statement() == ID_block &&
    !to_code_block(to_code(symbol.value)).has_operands() &&
    symbol.base_name == "operator=")
  {
    const code_typet &ft = to_code_type(symbol.type);
    const irep_idt class_id = symbol.type.get(ID_C_member_name);
    if(ft.parameters().size() == 2 && !class_id.empty())
    {
      const typet &pt = ft.parameters()[1].type();
      const bool is_ref_to_self =
        pt.id() == ID_pointer &&
        (pt.get_bool(ID_C_reference) || pt.get_bool(ID_C_rvalue_reference)) &&
        to_pointer_type(pt).base_type().id() == ID_struct_tag &&
        to_struct_tag_type(to_pointer_type(pt).base_type()).get_identifier() ==
          class_id;
      const symbolt *class_symbol = symbol_table.lookup(class_id);
      if(is_ref_to_self && class_symbol != nullptr)
      {
        // default_assignop_value refers to the source by the parameter name
        // "ref"; alias it to this operator's actual parameter (see the
        // defaulted-constructor elaboration above).
        cpp_idt &ref_id = function_scope.insert(irep_idt{"ref"});
        ref_id.identifier = ft.parameters()[1].get_identifier();
        ref_id.id_class = cpp_idt::id_classt::SYMBOL;
        ref_id.is_member = false;

        cpp_declaratort tmp_declarator;
        tmp_declarator.add_source_location() = symbol.location;
        default_assignop_value(
          *class_symbol, tmp_declarator, pt.get_bool(ID_C_rvalue_reference));
        symbol.value = tmp_declarator.value();
      }
    }
  }

  // [temp.deduct]/8 and the system-header analogue: when the
  // function whose body we are elaborating lives in a system
  // header, any typecheck failure is treated as SFINAE rather
  // than a user-visible compilation error.  This matches what
  // conforming implementations do when a non-template system
  // header function happens to be ill-formed against CBMC's
  // (deliberately incomplete) model of system headers — the
  // caller gets a "no usable body" symbol rather than a
  // diagnostic attributed to the header.
  //
  // User-code bodies use normal error propagation below.
  const std::string body_file = id2string(symbol.location.get_file());
  const bool is_system_header_body = is_library_body_file(body_file);

  std::optional<sfinae_contextt> syshdr_guard;
  if(is_system_header_body)
    syshdr_guard.emplace(*this);

  // N5008 [stmt.label]/1: labels have function scope -- a label name may
  // be reused in different functions.  The C type checker resets these
  // maps per function body (typecheck_function_body); this C++ entry
  // point must do the same, otherwise a label in one function makes the
  // same label name in the NEXT function a spurious "duplicate label"
  // (two functions with a 'zero:' error path, the big-int shape).
  labels_defined.clear();
  labels_used.clear();

  try
  {
    typecheck_code(to_code(symbol.value));
    if(
      symbol.type.id() == ID_code &&
      to_code_type(symbol.type).return_type().id() == ID_constructor)
    {
      add_constructor_unwinding(to_code(symbol.value));
    }
  }
  catch(int)
  {
    // N5008 [class.default.ctor]/2, [class.copy.ctor]/12,
    // [class.copy.assign]/7: an implicitly-declared special member
    // function whose implicit definition would be ill-formed (e.g. a
    // base class without a default constructor for the implicit
    // default constructor) is DEFINED AS DELETED -- the program is
    // only ill-formed if that deleted member is odr-used.  The front
    // end synthesizes these members eagerly and converting the body
    // then hard-errors on mere mention of the class (`struct D : B {}`
    // with B lacking a default constructor).  Treat the failure as a
    // deletion: drop the body and remove the member from the overload
    // set (ID_noaccess, the established `= delete` representation); a
    // later use then fails overload resolution naturally.
    // N5008 [dcl.fct.def.default]/5: an EXPLICITLY-DEFAULTED default
    // constructor whose implicit definition would be ill-formed is
    // likewise defined as deleted (`goto_symex_statet() = default;`
    // deriving from a class without a default constructor); recover it
    // through the same deletion path as the implicit one.
    const bool defaulted_default_ctor =
      symbol.type.id() == ID_code &&
      to_code_type(symbol.type).return_type().id() == ID_constructor &&
      symbol.value.get_bool("#defaulted_function");
    if(
      (symbol.type.get_bool("#is_implicit_ctor") || defaulted_default_ctor) &&
      to_code_type(symbol.type).parameters().size() == 1)
    {
      // Only the implicit DEFAULT constructor (this-parameter only) is
      // deleted this way: conversion of implicit copy/move constructors
      // can fail transiently (ordering of dependent conversions), and
      // deleting one changes which constructor overload later calls
      // select -- semantically visible (Constructor13).

      // A member deferred until odr-used ([dcl.fct.def.default]/5) is
      // converted because it is odr-used: it is defined as deleted, and
      // the program that refers to it is ill-formed
      // ([dcl.fct.def.delete]/2).
      if(odr_use_defined_defaulted_members.count(symbol.name) != 0)
      {
        error().source_location = symbol.location;
        error() << "the implicitly-defined default constructor of '"
                << symbol.base_name << "' is defined as deleted and is used"
                << eom;
        disable_access_control = saved_access_control;
        functions_being_typechecked.erase(symbol.name);
        throw 0;
      }

      // The diagnostics of the failed implicit definition are not
      // errors -- the member is merely deleted; restore the count.
      get_message_handler().set_message_count(
        messaget::M_ERROR, errors_before_conversion);
      symbol.value.make_nil();
      const irep_idt &class_id = symbol.type.get(ID_C_member_name);
      if(!class_id.empty())
      {
        symbolt &class_symbol = symbol_table.get_writeable_ref(class_id);
        for(auto &c : to_struct_union_type(class_symbol.type).components())
        {
          if(c.get_name() == symbol.name)
          {
            c.set(ID_access, ID_noaccess);
            break;
          }
        }
      }
      disable_access_control = saved_access_control;
      functions_being_typechecked.erase(symbol.name);
      deferred_typechecking.erase(symbol.name);
      return;
    }

    // N5008 [temp.inst]/4, [temp.point]/8: a member's definition is
    // instantiated when it is odr-used, and its point of instantiation may
    // be the END of the translation unit -- so a body converted EAGERLY (an
    // auto-returning member of a class instance, converted during that
    // class's elaboration; a callee instantiated on the way) may fail only
    // because some class it uses is still incomplete right now:
    // view_interface<ref_view<int[5]>> is elaborated as a BASE of
    // ref_view<int[5]>, its members' `_M_derived().begin()` name the
    // not-yet-complete derived class, and the ranges::begin(ref_view&)
    // instance created on the way inherited the failure.  Dropping such
    // bodies made `arr | views::take(3)`'s begin() return `auto`.  While a
    // class is being elaborated, restore the parsed body and re-queue it
    // for the end-of-unit drain, where every class is complete (a call site
    // reached before then converts it on demand, as for any
    // not-yet-converted auto member).  The speculative caller
    // (add_method_body) suppresses the attempt's diagnostics.
    if(compound_body_depth > 0)
    {
      symbol.value = original_body;
      method_bodies.push_back(
        method_bodyt(&symbol, template_map, instantiation_stack));
      functions_being_typechecked.erase(symbol.name);
      disable_access_control = saved_access_control;
      return;
    }

    // For system headers, clear the broken body and return.
    // For user code, re-throw.  The `syshdr_guard` destructor (if
    // engaged) runs on the way out and restores handler/error
    // count; the user-code rethrow keeps going to the caller.
    if(is_system_header_body)
    {
      // Before giving up: a class-template instance member can be left with
      // the WRONG overload's out-of-line body (attached by an earlier
      // base-name-only match), e.g. the input-iterator basic_string::
      // _M_construct body (which references `__beg`) ending up on the fill
      // _M_construct(size_type, _CharT) member, so its conversion fails with
      // "symbol '__beg' is unknown" and the member silently becomes a no-op.
      // If a *unique* out-of-line definition whose signature (parameter
      // arity) matches this member exists, and it is a different definition
      // from the one currently attached (different source location), adopt
      // that signature-matched body and the definition's parameter names and
      // re-type-check.  Doing this only on failure leaves correctly-converting
      // members untouched.  Per N5008 [over.match] the definition belonging to
      // a member is the one whose signature matches it; per [dcl.fct]/3
      // parameter names are not part of the type, so the body must use the
      // definition's names.
      if(!symbol.type.get(ID_C_member_name).empty())
      {
        std::vector<irep_idt> def_param_names;
        const std::optional<exprt> matched =
          instantiate_matching_member_body(symbol, def_param_names);
        if(
          matched.has_value() &&
          !matched->source_location().get_line().empty() &&
          matched->source_location().get_line() !=
            symbol.value.source_location().get_line())
        {
          symbol.value = *matched;
          code_typet::parameterst &params = function_type.parameters();
          const std::size_t off =
            (!params.empty() && params.front().get_this()) ? 1 : 0;
          for(std::size_t i = 0;
              i < def_param_names.size() && off + i < params.size();
              ++i)
          {
            if(!def_param_names[i].empty())
              params[off + i].set_base_name(def_param_names[i]);
          }
          // Re-type-check with the corrected body in a fresh scope.  The
          // source-location guard above prevents this from looping: after the
          // adoption the attached body's location equals the match's.  If the
          // corrected body still cannot be converted (e.g. it transitively
          // instantiates something CBMC cannot model), fall back to the
          // no-body state exactly as if no repair had been attempted, so the
          // repair can never make a system-header member worse.
          functions_being_typechecked.erase(symbol.name);
          try
          {
            convert_function(symbol);
            return;
          }
          catch(...)
          {
            // fall through to the no-body state below
          }
        }
      }
      // A system-header body that fails outside any class elaboration is
      // retried once in the end-of-unit drain (see the [temp.inst]/4 note
      // above); only a second failure leaves the function bodyless.
      if(body_conversion_retried.insert(symbol.name).second)
      {
        symbol.value = original_body;
        method_bodies.push_back(
          method_bodyt(&symbol, template_map, instantiation_stack));
        functions_being_typechecked.erase(symbol.name);
        return;
      }
      // A bodyless function is a havoc stub downstream: every call returns
      // nondet and assigns nothing.  Say so -- after releasing the
      // system-header guard, which suppressed the failed conversion's
      // diagnostics (and would suppress this one).  Not for a member with
      // a trailing requires-clause: its constraints may simply be
      // unsatisfied for this specialization, in which case the definition
      // is never instantiated ([temp.inst]/4) and the failure is expected.
      syshdr_guard.reset();
      if(!symbol.type.get_bool("#constrained"))
      {
        report_dropped_body(symbol, "unsupported construct");
      }
      symbol.value.make_nil();
      functions_being_typechecked.erase(symbol.name);
      return;
    }
    throw;
  }

  // N5008 [dcl.spec.auto.general]/11: no non-discarded return statement --
  // the return type is deduced as from `return;' at the closing brace: void
  // for `auto' / `decltype(auto)', ill-formed for `auto *' and the like.
  if(has_auto(function_type.return_type()))
  {
    if(has_auto(return_type))
    {
      if(
        return_type.id() != ID_auto &&
        !(return_type.id() == ID_decltype && return_type.get_bool("#auto")))
      {
        error().source_location = symbol.location;
        error() << "cannot deduce '" << to_string(return_type)
                << "' from void()" << eom;
        throw 0;
      }
      return_type = void_type();
    }
    function_type.return_type() = return_type;
  }

  symbol.value.type()=symbol.type;

  // Mark this body as fully type-checked.  The final half-converted
  // sweep in cpp_typecheckt::typecheck() uses the absence of this flag
  // to find instances whose eager conversion was absorbed by candidate
  // matching (see the [dcl.spec.auto]/11 note there).
  symbol.value.set("#cpp_converted", true);

  disable_access_control = saved_access_control;

  deferred_typechecking.erase(symbol.name);
}

/// for function overloading
irep_idt cpp_typecheckt::function_identifier(const typet &type)
{
  const code_typet &function_type=
    to_code_type(template_subtype(type));

  const code_typet::parameterst &parameters=
    function_type.parameters();

  std::string result;
  bool first=true;

  result+='(';

  // the name of the function should not depend on
  // the class name that is encoded in the type of this,
  // but we must distinguish "const" and "non-const" member
  // functions

  code_typet::parameterst::const_iterator it=
    parameters.begin();

  if(it != parameters.end() && it->get_this())
  {
    const typet &pointer=it->type();
    const typet &symbol = to_pointer_type(pointer).base_type();
    if(symbol.get_bool(ID_C_constant))
      result += "$const";
    if(symbol.get_bool(ID_C_volatile))
      result += "$volatile";
    // N5008 [defns.signature.member]: the ref-qualifier is part of a member
    // function's signature; `f() &' and `f() &&' are distinct overloads
    // ([over.match.funcs.general]/4)
    const irep_idt &ref_qualifier = function_type.get(ID_C_ref_qualifier);
    if(ref_qualifier == "&")
      result += "$lref";
    else if(ref_qualifier == "&&")
      result += "$rref";
    result += id2string(ID_this);
    first=false;
    it++;
  }

  // we skipped the "this", on purpose!

  for(; it!=parameters.end(); it++)
  {
    if(first)
      first=false;
    else
      result+=',';
    typet tmp_type=it->type();
    // C/C++ function parameters of function type decay to
    // pointer-to-function.  Normalise here so that the identifier
    // is the same regardless of declaration style.
    if(tmp_type.id() == ID_code)
      tmp_type = pointer_type(tmp_type);
    // Top-level const/volatile on parameters does not affect the
    // function signature per [dcl.fct]/5.
    tmp_type.remove(ID_C_constant);
    tmp_type.remove(ID_C_volatile);
    result += cpp_type2name(tmp_type);
  }

  result+=')';

  return result;
}
