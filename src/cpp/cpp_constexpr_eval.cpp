/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// Constant evaluation of constexpr function calls (N5008 [expr.const])

#include "cpp_constexpr_eval.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include "itanium_abi_cpp_zero_initializer.h"

#include <map>
#include <optional>

// N5008 [expr.const]/5, [class.temporary]: the value of a temporary of
// literal class type -- for a class-type template argument
// ([temp.arg.nontype]/1), a value-initialized `T()' or a constexpr object's
// initializer.  Handles a single initializing operand (a struct constant or
// a call yielding one) and an `initializer' constructing the object (a
// constructor call, or the member assignments of a synthesized default
// constructor with the value-initialization zero prefix).
static exprt evaluate_temporary_object(
  const exprt &expr,
  const symbol_table_baset &symbol_table,
  const namespacet &ns,
  const std::function<bool(const irep_idt &)> &ensure_definition)
{
  // The temporary's value: a single operand is the initializing
  // expression (a struct constant, or a call yielding one); otherwise the
  // `initializer' code constructs the object -- a constructor call, or the
  // statements of a synthesized default constructor (member assignments
  // from default member initializers, [class.default.ctor]/4), optionally
  // preceded by the zero-initialization of value-initialization
  // ([dcl.init.general]/9.1).
  if(expr.operands().size() == 1)
  {
    const exprt &value = expr.operands().front();
    if(value.id() == ID_struct || value.is_constant())
      return value;
    return try_evaluate_constexpr(value, symbol_table, ns, ensure_definition);
  }
  const irept &init = expr.find(ID_initializer);
  if(expr.type().id() != ID_struct_tag)
    return nil_exprt();
  const auto zero =
    itanium_abi_cpp_zero_initializer(expr.type(), source_locationt{}, ns);
  if(!zero.has_value() || zero->id() != ID_struct)
    return nil_exprt();
  exprt object = *zero;
  // no initializer at all: a trivially default-constructed temporary (an
  // empty class, a class without default member initializers)
  if(init.is_nil())
    return object;
  if(init.id() != ID_code)
    return nil_exprt();
  const struct_typet &object_type =
    ns.follow_tag(to_struct_tag_type(expr.type()));
  std::function<bool(const exprt &, const exprt &)> assign;
  std::function<bool(const codet &)> run = [&](const codet &code) -> bool
  {
    const irep_idt &statement = code.get_statement();
    if(statement == ID_block)
    {
      for(const auto &op : code.operands())
        if(!run(to_code(op)))
          return false;
      return true;
    }
    if(statement == ID_skip)
      return true;
    if(statement == ID_expression && code.operands().size() == 1)
    {
      const exprt &e = code.op0();
      if(e.id() != ID_side_effect)
        return false;
      if(e.get(ID_statement) == ID_function_call)
      {
        // a constructor call on the temporary: it computes the whole
        // object (over a zero-initialized one, as the evaluator does)
        const exprt r =
          try_evaluate_constexpr(e, symbol_table, ns, ensure_definition);
        if(r.id() != ID_struct)
          return false;
        object = r;
        return true;
      }
      // a default member initializer, lowered to `new_object.m = value'
      if(e.get(ID_statement) == ID_assign && e.operands().size() == 2)
        return assign(e.operands()[0], e.operands()[1]);
      return false;
    }
    if(statement == ID_assign && code.operands().size() == 2)
      return assign(code.op0(), code.op1());
    return false;
  };
  assign = [&](const exprt &lhs, const exprt &rhs_in) -> bool
  {
    exprt rhs = rhs_in;
    // a bit-field member is assigned its value cast to the bit-field type
    // ([class.bit]); evaluate the underlying value, the member's type is
    // re-applied below
    while(rhs.id() == ID_typecast && rhs.type().id() == ID_c_bit_field)
      rhs = to_typecast_expr(rhs).op();
    if(!(rhs.id() == ID_struct || rhs.is_constant()))
    {
      // a call (or temporary) is evaluated; anything else is an expression
      // over constants (`(unsigned short)(bool)false' for a bit-field's
      // `{false}') that the simplifier folds
      if(rhs.id() == ID_side_effect)
        rhs = try_evaluate_constexpr(rhs, symbol_table, ns, ensure_definition);
      else
        simplify(rhs, ns);
      if(!(rhs.id() == ID_struct || rhs.is_constant()))
        return false;
    }
    if(lhs.id() == ID_new_object)
    {
      if(rhs.id() != ID_struct)
        return false;
      object = rhs;
      return true;
    }
    if(
      lhs.id() == ID_member &&
      to_member_expr(lhs).compound().id() == ID_new_object &&
      object_type.has_component(to_member_expr(lhs).get_component_name()))
    {
      const std::size_t index = object_type.data_component_number(
        to_member_expr(lhs).get_component_name());
      if(index >= object.operands().size())
        return false;
      object.operands()[index] =
        typecast_exprt::conditional_cast(rhs, object.operands()[index].type());
      simplify(object.operands()[index], ns);
      return true;
    }
    return false;
  };
  if(!run(static_cast<const codet &>(init)))
    return nil_exprt();
  return object;
}

// N5008 [expr.const], [dcl.constexpr]/6: the value of the object a member
// function is called on, when that is a constexpr object -- the address of a
// struct constant, or of a const/constexpr symbol whose value is a struct
// constant.  Returns nil when the call is not such a member function call.
static exprt constexpr_this_object_value(
  const code_typet &function_type,
  const exprt::operandst &arguments,
  const symbol_table_baset &symbol_table)
{
  const bool has_this_parameter = !function_type.parameters().empty() &&
                                  function_type.parameters().front().get_this();
  if(
    !has_this_parameter || arguments.empty() ||
    arguments.front().id() != ID_address_of)
    return nil_exprt();
  const exprt &object = to_address_of_expr(arguments.front()).object();
  if(object.id() == ID_struct)
    return object;
  if(object.id() == ID_symbol)
  {
    const symbolt *object_symbol =
      symbol_table.lookup(to_symbol_expr(object).get_identifier());
    if(
      object_symbol != nullptr && !object_symbol->is_type &&
      (object_symbol->type.get_bool(ID_C_constant) ||
       object_symbol->is_macro) &&
      object_symbol->value.id() == ID_struct)
    {
      return object_symbol->value;
    }
  }
  return nil_exprt();
}

// N5008 [expr.add]/4, [expr.unary.op]/1, [expr.const]: a pointer INTO an
// array whose elements are constants -- a string literal, an array constant,
// or a static object with an array constant value (a constexpr array, the
// backing array of a std::initializer_list, [dcl.init.list]/6) -- is tracked
// as `&arr[i]' (address_of an index of the array expression); arithmetic
// moves the index, `*p' reads the element, two pointers into the same array
// compare by index.
struct array_pointert
{
  exprt array; // string_constant, array constant, or a symbol
  mp_integer index;
};

/// Whether \p symbol is an array object whose value a constant evaluation
/// may read: one with static storage duration initialized by an array
/// constant, or -- N5008 [expr.const]/4, /7 -- a constexpr variable of any
/// storage duration, which is usable in constant expressions (constexpr
/// declares the object const, [dcl.constexpr]/6, and its initializer is a
/// constant expression).  The latter is libc++'s `constexpr _CCC
/// __type_kinds[] = {...}' local passed by reference to the constexpr
/// __compute_comp_type in __get_comp_type.
static bool constant_array_symbol(const symbolt &symbol)
{
  if(symbol.is_type || symbol.value.id() != ID_array)
    return false;
  if(symbol.is_static_lifetime)
    return true;
  if(
    symbol.type.id() != ID_array ||
    !to_array_type(symbol.type).element_type().get_bool(ID_C_constant))
  {
    return false;
  }
  for(const auto &element : symbol.value.operands())
    if(!element.is_constant())
      return false;
  return true;
}

/// The constant array value a tracked array pointer's array denotes: the
/// expression itself for a literal, the symbol's value for a static object.
static exprt array_pointer_value(
  const array_pointert &ap,
  const symbol_table_baset &symbol_table)
{
  if(ap.array.id() == ID_string_constant || ap.array.id() == ID_array)
    return ap.array;
  if(ap.array.id() == ID_symbol)
  {
    const symbolt *symbol =
      symbol_table.lookup(to_symbol_expr(ap.array).get_identifier());
    if(symbol != nullptr && constant_array_symbol(*symbol))
      return symbol->value;
  }
  return nil_exprt();
}

/// Is \p e an array whose elements a tracked pointer can read?
static bool
is_constant_array_object(const exprt &e, const symbol_table_baset &symbol_table)
{
  if(e.type().id() != ID_array)
    return false;
  if(e.id() == ID_string_constant || e.id() == ID_array)
    return true;
  if(e.id() == ID_symbol)
  {
    const symbolt *symbol =
      symbol_table.lookup(to_symbol_expr(e).get_identifier());
    return symbol != nullptr && constant_array_symbol(*symbol);
  }
  return false;
}

/// The array and index a tracked array pointer denotes, or nothing
/// The value of an integer constant, also through integer conversions
/// (`(int)1')
static std::optional<mp_integer> integer_constant(const exprt &e)
{
  if(e.is_constant())
    return numeric_cast<mp_integer>(to_constant_expr(e));
  if(
    e.id() == ID_typecast &&
    (e.type().id() == ID_signedbv || e.type().id() == ID_unsignedbv))
    return integer_constant(to_typecast_expr(e).op());
  return std::nullopt;
}

static std::optional<array_pointert>
array_pointer(const exprt &e, const symbol_table_baset &symbol_table)
{
  // a qualification conversion (`char *' to `const char *', [conv.qual]):
  // the same pointer
  if(
    e.id() == ID_typecast && e.type().id() == ID_pointer &&
    to_typecast_expr(e).op().type().id() == ID_pointer)
  {
    return array_pointer(to_typecast_expr(e).op(), symbol_table);
  }
  // `&a[i] + n' (the simplifier's form of `&a[i + n]')
  if(
    (e.id() == ID_plus || e.id() == ID_minus) && e.operands().size() == 2 &&
    e.type().id() == ID_pointer)
  {
    auto ap = array_pointer(to_binary_expr(e).op0(), symbol_table);
    const auto n = integer_constant(to_binary_expr(e).op1());
    if(!ap.has_value() || !n.has_value())
      return std::nullopt;
    ap->index += e.id() == ID_plus ? *n : -*n;
    return ap;
  }
  if(e.id() != ID_address_of || e.operands().size() != 1)
    return std::nullopt;
  const exprt &object = to_address_of_expr(e).object();
  if(is_constant_array_object(object, symbol_table))
    return array_pointert{object, 0};
  if(
    object.id() != ID_index ||
    !is_constant_array_object(to_index_expr(object).array(), symbol_table))
  {
    return std::nullopt;
  }
  const auto index = integer_constant(to_index_expr(object).index());
  if(!index.has_value())
    return std::nullopt;
  return array_pointert{to_index_expr(object).array(), *index};
}

static exprt
make_array_pointer(const array_pointert &ap, const typet &pointer_type)
{
  return address_of_exprt{
    index_exprt{
      ap.array,
      from_integer(ap.index, c_index_type()),
      to_array_type(ap.array.type()).element_type()},
    to_pointer_type(pointer_type)};
}

/// `*p' for a tracked array pointer: the element (a string literal's
/// terminating null included, [lex.string]/9), or nothing when the index is
/// out of range
static std::optional<exprt> array_pointer_deref(
  const array_pointert &ap,
  const symbol_table_baset &symbol_table,
  const namespacet &ns)
{
  const exprt value = array_pointer_value(ap, symbol_table);
  if(value.is_nil() || value.type().id() != ID_array)
    return std::nullopt;
  const auto size = numeric_cast<mp_integer>(
    to_constant_expr(to_array_type(value.type()).size()));
  if(!size.has_value() || ap.index < 0 || ap.index >= *size)
    return std::nullopt;
  exprt c = index_exprt{
    value,
    from_integer(ap.index, c_index_type()),
    to_array_type(value.type()).element_type()};
  simplify(c, ns);
  if(!c.is_constant())
    return std::nullopt;
  return c;
}

bool is_constexpr_call_argument(
  const exprt &e,
  const symbol_table_baset &symbol_table)
{
  if(e.id() == ID_symbol)
    return false;
  // [expr.const]/11: the address of (an element of) an object with static
  // storage duration -- a constexpr array, the backing array of a
  // std::initializer_list argument (`{ &arr[0], 3 }', [dcl.init.list]/6);
  // such a pointer is tracked by array and index
  if(e.id() == ID_address_of && array_pointer(e, symbol_table))
    return true;
  for(const auto &op : e.operands())
    if(!is_constexpr_call_argument(op, symbol_table))
      return false;
  return true;
}

/// The state of one constexpr function evaluation: the tracked variables and
/// the interpreter over the function body (bounded loops, the statement and
/// expression forms a constexpr function may contain).
class constexpr_interpretert
{
public:
  constexpr_interpretert(
    const symbol_table_baset &_symbol_table,
    const namespacet &_ns,
    const std::function<bool(const irep_idt &)> &_ensure_definition,
    const typet &_constructed_type)
    : symbol_table(_symbol_table),
      ns(_ns),
      ensure_definition(_ensure_definition),
      constructed_type(_constructed_type)
  {
  }

  const symbol_table_baset &symbol_table;
  const namespacet &ns;
  const std::function<bool(const irep_idt &)> &ensure_definition;
  const typet &constructed_type;

  // parameter -> constant value; for a constructor or a member function on a
  // constexpr object, `this' -> the object's value under this_id
  std::map<irep_idt, exprt> vars;
  irep_idt this_id;

  // N5008 [implimits] recommends 1 048 576 full-expression evaluations in a
  // core constant expression; loops are bounded well below that -- an
  // evaluation that needs more is left to run time.
  static const int max_loop_iterations = 4096;

  // A tracked value: a scalar constant, or an aggregate of constants (the
  // `constexpr bool found[] = {__is_same(T, Ts)...}` local of libstdc++'s
  // __find_uniq_type_in_pack, read back through `found[i]`).
  static bool is_constant_value(const exprt &e)
  {
    if(e.is_constant())
      return true;
    if(e.id() == ID_array || e.id() == ID_struct)
    {
      for(const auto &op : e.operands())
        if(!op.is_constant())
          return false;
      return true;
    }
    return false;
  }

  /// As is_constant_value, also for an aggregate with aggregate members or
  /// members that point into a constant array ([expr.const]/14: a pointer
  /// to an element of a string literal is a permitted result) -- the
  /// `const C *' of a string_view built from a literal.
  static bool
  is_constant_value(const exprt &e, const symbol_table_baset &symbol_table)
  {
    if(e.is_constant() || array_pointer(e, symbol_table).has_value())
      return true;
    if(e.id() == ID_array || e.id() == ID_struct)
    {
      for(const auto &op : e.operands())
        if(!is_constant_value(op, symbol_table))
          return false;
      return true;
    }
    return false;
  }

  // Set when a statement's effect could not be tracked or a condition could
  // not be decided: the evaluation is then abandoned as a whole.  Continuing
  // with stale variable values produced WRONG results (`++p; return *p'
  // returned the character before the increment; `while(*p++) ++n' over a
  // string literal returned 0), and a static_assert built on them failed.
  bool failed = false;

  // Apply an assignment-like side effect (`=`, compound assignment,
  // `++`/`--`) to a tracked variable.  Returns false when the effect cannot
  // be tracked (the caller then gives up on the evaluation).
  // `this->m` -- the object under construction is tracked by value, so a
  // member access through `this` reads the tracked struct's component.
  std::optional<std::size_t> this_member_index(const exprt &e) const
  {
    if(this_id.empty() || e.id() != ID_member)
      return std::nullopt;
    const exprt &compound = to_member_expr(e).compound();
    if(
      compound.id() != ID_dereference || compound.operands().size() != 1 ||
      compound.operands()[0].id() != ID_symbol ||
      to_symbol_expr(compound.operands()[0]).get_identifier() != this_id)
    {
      return std::nullopt;
    }
    const auto it = vars.find(this_id);
    if(it == vars.end() || it->second.id() != ID_struct)
      return std::nullopt;
    const struct_typet &st =
      ns.follow_tag(to_struct_tag_type(constructed_type));
    if(!st.has_component(to_member_expr(e).get_component_name()))
      return std::nullopt;
    return st.data_component_number(to_member_expr(e).get_component_name());
  }

  bool apply_side_effect(const exprt &e)
  {
    if(e.id() != ID_side_effect)
      return true; // no effect to apply (e.g. a plain expression)
    const irep_idt &st = e.get(ID_statement);
    // `this->m = v` ([class.base.init]: a mem-initializer, lowered to an
    // assignment through `this`; or an assignment in the constructor body)
    if(st == ID_assign && e.operands().size() == 2)
    {
      if(const auto idx = this_member_index(e.operands()[0]))
      {
        exprt rhs = eval(e.operands()[1]);
        if(!is_constant_value(rhs, symbol_table))
          return false;
        exprt &obj = vars.at(this_id);
        if(*idx >= obj.operands().size())
          return false;
        obj.operands()[*idx] =
          typecast_exprt::conditional_cast(rhs, obj.operands()[*idx].type());
        simplify(obj.operands()[*idx], ns);
        return true;
      }
    }
    // N5008 [expr.const]/5 (C++14 relaxed constexpr): an assignment or
    // increment of an ELEMENT of a local array object whose lifetime began
    // within the evaluation -- `int __seen[_CCC_Size] = {}; ... ++__seen[t]'
    // in libc++'s __compute_comp_type.  Apply the effect to the element
    // through a scratch variable and store the result back.
    if(!e.operands().empty() && e.operands()[0].id() == ID_index)
    {
      const index_exprt &element = to_index_expr(e.operands()[0]);
      if(element.array().id() != ID_symbol)
        return false;
      const auto array_it =
        vars.find(to_symbol_expr(element.array()).get_identifier());
      if(array_it == vars.end() || array_it->second.id() != ID_array)
        return false;
      const exprt index = eval(element.index());
      const auto i = index.is_constant()
                       ? numeric_cast<mp_integer>(to_constant_expr(index))
                       : std::nullopt;
      if(
        !i.has_value() || *i < 0 ||
        *i >= mp_integer{array_it->second.operands().size()})
      {
        return false; // [expr.const]/5.8: undefined behaviour is not constant
      }
      const std::size_t position = numeric_cast_v<std::size_t>(*i);
      const irep_idt scratch{"#constexpr_array_element"};
      const exprt &old_value = array_it->second.operands()[position];
      vars[scratch] = old_value;
      exprt on_scratch = e;
      on_scratch.operands()[0] = symbol_exprt{scratch, old_value.type()};
      const bool applied = apply_side_effect(on_scratch);
      if(applied)
        array_it->second.operands()[position] = vars.at(scratch);
      vars.erase(scratch);
      return applied;
    }
    if(e.operands().empty() || e.operands()[0].id() != ID_symbol)
      return false;
    const irep_idt var = to_symbol_expr(e.operands()[0]).get_identifier();
    if(st == ID_assign)
    {
      if(e.operands().size() != 2)
        return false;
      exprt rhs = eval(e.operands()[1]);
      // also a pointer into a constant array (`e = "U8"')
      if(!is_constant_value(rhs, symbol_table))
        return false;
      vars[var] = rhs;
      return true;
    }
    const auto cur = vars.find(var);
    if(cur == vars.end())
      return false;
    if(const auto sp = array_pointer(cur->second, symbol_table))
    {
      // pointer arithmetic on a pointer into a string literal
      mp_integer delta;
      if(st == ID_preincrement || st == ID_postincrement)
        delta = 1;
      else if(st == ID_predecrement || st == ID_postdecrement)
        delta = -1;
      else if(
        (st == ID_assign_plus || st == ID_assign_minus) &&
        e.operands().size() == 2)
      {
        const exprt rhs = eval(e.operands()[1]);
        const auto n = rhs.is_constant()
                         ? numeric_cast<mp_integer>(to_constant_expr(rhs))
                         : std::nullopt;
        if(!n.has_value())
          return false;
        delta = st == ID_assign_plus ? *n : -*n;
      }
      else
        return false;
      array_pointert moved = *sp;
      moved.index += delta;
      vars[var] = make_array_pointer(moved, cur->second.type());
      return true;
    }
    if(!cur->second.is_constant())
      return false;
    irep_idt op;
    exprt rhs;
    if(
      st == ID_preincrement || st == ID_postincrement ||
      st == ID_predecrement || st == ID_postdecrement)
    {
      op =
        (st == ID_preincrement || st == ID_postincrement) ? ID_plus : ID_minus;
      rhs = from_integer(1, cur->second.type());
    }
    else if(e.operands().size() == 2)
    {
      const std::string s = id2string(st);
      if(s.size() < 7 || s.substr(0, 6) != "assign")
        return false;
      op = irep_idt{s.substr(6)}; // `assign+` -> `+`
      if(
        op != ID_plus && op != ID_minus && op != ID_mult && op != ID_div &&
        op != ID_mod && op != ID_shl && op != ID_shr && op != ID_bitand &&
        op != ID_bitor && op != ID_bitxor)
      {
        return false;
      }
      rhs = eval(e.operands()[1]);
      if(!rhs.is_constant())
        return false;
      rhs = typecast_exprt::conditional_cast(rhs, cur->second.type());
    }
    else
      return false;
    exprt result = binary_exprt{cur->second, op, rhs, cur->second.type()};
    simplify(result, ns);
    if(!result.is_constant())
      return false;
    vars[var] = result;
    return true;
  }

  /// A tracked variable's value that is the address of ANOTHER tracked
  /// variable (a reference bound to a local or parameter, `auto &&__range =
  /// xs' of a range-for) denotes that variable: return its value, else nil
  exprt referenced_value(const exprt &value) const
  {
    if(
      value.id() != ID_address_of || value.operands().size() != 1 ||
      to_address_of_expr(value).object().id() != ID_symbol)
    {
      return nil_exprt();
    }
    const auto it = vars.find(
      to_symbol_expr(to_address_of_expr(value).object()).get_identifier());
    return it == vars.end() ? static_cast<exprt>(nil_exprt()) : it->second;
  }

  /// Can \p value be tracked as a variable's value?  A constant, an aggregate
  /// of constants, a pointer into a constant array, or a reference to a
  /// tracked variable.
  bool is_trackable(const exprt &value) const
  {
    return is_constant_value(value) ||
           array_pointer(value, symbol_table).has_value() ||
           referenced_value(value).is_not_nil();
  }

  /// The value to store for `lhs = rhs' / `T x = rhs': a reference bound to
  /// a tracked variable ([dcl.init.ref]: `auto &&__range = xs' of a
  /// range-for) is kept as the ALIAS `&xs', not evaluated to a copy, so
  /// later reads through it see the variable; anything else is evaluated.
  exprt eval_initializer(const exprt &rhs)
  {
    if(referenced_value(rhs).is_not_nil())
      return rhs;
    return eval(rhs);
  }

  exprt eval(const exprt &e)
  {
    // N5008 [expr.type.conv]/2: `T{...}' is a prvalue of class type T whose
    // value is its initializer; the front end wraps the struct in a compound
    // literal (`return P{1, 2};' in a constexpr function)
    if(
      e.id() == ID_compound_literal && e.operands().size() == 1 &&
      e.type() == to_unary_expr(e).op().type())
    {
      return eval(to_unary_expr(e).op());
    }
    // N5008 [expr.unary.op]/3: `&a[i]' denotes an object, not a value: only
    // the index is evaluated (evaluating `a[i]' read the element and made
    // `const char *e = "U8"' the address of a character constant)
    if(
      e.id() == ID_address_of && e.operands().size() == 1 &&
      to_address_of_expr(e).object().id() == ID_index &&
      is_constant_array_object(
        to_index_expr(to_address_of_expr(e).object()).array(), symbol_table))
    {
      exprt result = e;
      exprt &index = to_index_expr(to_address_of_expr(result).object()).index();
      index = eval(index);
      simplify(index, ns);
      return result;
    }
    if(const auto idx = this_member_index(e))
    {
      const exprt &obj = vars.at(this_id);
      if(*idx < obj.operands().size())
        return obj.operands()[*idx];
      return e;
    }
    if(e.id() == ID_symbol)
    {
      auto it = vars.find(to_symbol_expr(e).get_identifier());
      if(it != vars.end())
      {
        // `this' is tracked by the object's VALUE; the expression `this' is
        // the object's address (`*this', `&*this', `this->m' read through
        // this_member_index above)
        if(it->first == this_id && e.type().id() == ID_pointer)
          return address_of_exprt{it->second, to_pointer_type(e.type())};
        // a reference to a tracked variable: the address of its value (so
        // a member call through it binds `this' to that value)
        const exprt referenced = referenced_value(it->second);
        if(referenced.is_not_nil())
          return address_of_exprt{referenced, to_pointer_type(e.type())};
        return it->second;
      }
      // a `constexpr` variable (a static data member `value`, an
      // enumerator) is a macro whose initializer is its value
      const symbolt *var_sym =
        symbol_table.lookup(to_symbol_expr(e).get_identifier());
      // N5008 [expr.const]/8-9: so is a non-volatile const variable of
      // integral or enumeration type initialized with a constant
      // (`const int value = 1;' read by a constexpr function)
      const auto potentially_constant = [](const symbolt &sym)
      {
        const typet &t = sym.type;
        return t.get_bool(ID_C_constant) && !t.get_bool(ID_C_volatile) &&
               (t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
                t.id() == ID_c_bool || t.id() == ID_bool ||
                t.id() == ID_c_enum_tag);
      };
      if(
        var_sym != nullptr && !var_sym->is_type &&
        (var_sym->is_macro || potentially_constant(*var_sym)) &&
        var_sym->value.is_not_nil() && var_sym->value.id() != ID_code)
      {
        exprt value = var_sym->value;
        simplify(value, ns);
        if(is_constant_value(value))
          return value;
      }
      return e;
    }
    // dereference(symbol) where symbol maps to a constant:
    // the parameter is a reference, unwrap the dereference.
    if(
      e.id() == ID_dereference && e.operands().size() == 1 &&
      e.operands()[0].id() == ID_symbol)
    {
      auto it = vars.find(to_symbol_expr(e.operands()[0]).get_identifier());
      if(it != vars.end() && it->second.is_constant())
        return it->second;
      if(it != vars.end())
      {
        // `*this' is the tracked object's value
        if(it->first == this_id)
          return it->second;
        // a reference to a tracked variable denotes that variable
        const exprt referenced = referenced_value(it->second);
        if(referenced.is_not_nil())
          return referenced;
        // N5008 [dcl.init.ref]: a REFERENCE TO ARRAY parameter
        // (`const bool (&m)[N]', libc++'s `__find_idx') bound to a static
        // constexpr array denotes the whole array -- its constant value --
        // so `m[i]' below indexes the array constant ([expr.const]/5.9)
        if(
          e.type().id() == ID_array && it->second.id() == ID_address_of &&
          is_constant_array_object(
            to_address_of_expr(it->second).object(), symbol_table))
        {
          const exprt value = array_pointer_value(
            array_pointert{to_address_of_expr(it->second).object(), 0},
            symbol_table);
          if(value.is_not_nil())
            return value;
        }
        if(const auto sp = array_pointer(it->second, symbol_table))
        {
          if(const auto c = array_pointer_deref(*sp, symbol_table, ns))
            return *c;
          failed = true;
          return e;
        }
      }
    }
    // `*p++', `*++p', `p++ == q': an increment or decrement of a tracked
    // variable inside an expression ([expr.post.incr], [expr.pre.incr]) --
    // the value is the old (post) or the new (pre) one
    if(
      e.id() == ID_side_effect &&
      (e.get(ID_statement) == ID_preincrement ||
       e.get(ID_statement) == ID_postincrement ||
       e.get(ID_statement) == ID_predecrement ||
       e.get(ID_statement) == ID_postdecrement) &&
      e.operands().size() == 1 && e.operands()[0].id() == ID_symbol)
    {
      const irep_idt var = to_symbol_expr(e.operands()[0]).get_identifier();
      const auto before = vars.find(var);
      if(before == vars.end())
      {
        failed = true;
        return e;
      }
      const exprt old_value = before->second;
      if(!apply_side_effect(e))
      {
        failed = true;
        return e;
      }
      const bool post = e.get(ID_statement) == ID_postincrement ||
                        e.get(ID_statement) == ID_postdecrement;
      return post ? old_value : vars.at(var);
    }
    // `*p' where p evaluates to a pointer into a string literal
    if(e.id() == ID_dereference && e.operands().size() == 1)
    {
      const exprt pointer = eval(e.operands()[0]);
      if(const auto sp = array_pointer(pointer, symbol_table))
      {
        if(const auto c = array_pointer_deref(*sp, symbol_table, ns))
          return *c;
        failed = true;
        return e;
      }
    }
    // N5008 [expr.cond]/1, [expr.log.and]/1, [expr.log.or]/1: only the
    // selected operand is evaluated.  Evaluating both branches of
    // `n < 2 ? n : fib(n - 1) + fib(n - 2)` made the recursion exponential
    // in the argument (and the unselected branch may not be a constant
    // expression at all, e.g. a divide by zero guarded by the condition).
    if(e.id() == ID_if && e.operands().size() == 3)
    {
      exprt cond = eval(to_if_expr(e).cond());
      if(cond.is_true())
        return eval(to_if_expr(e).true_case());
      if(cond.is_false())
        return eval(to_if_expr(e).false_case());
      if(cond.is_constant())
      {
        return eval(
          to_constant_expr(cond).is_zero() ? to_if_expr(e).false_case()
                                           : to_if_expr(e).true_case());
      }
    }
    if((e.id() == ID_and || e.id() == ID_or) && e.operands().size() >= 2)
    {
      const bool is_and = e.id() == ID_and;
      exprt result = e;
      for(auto &op : result.operands())
      {
        op = eval(op);
        if(is_and && op.is_false())
          return false_exprt();
        if(!is_and && op.is_true())
          return true_exprt();
        if(!op.is_true() && !op.is_false())
          break; // not decidable here: fall back to the simplifier
      }
      simplify(result, ns);
      return result;
    }
    if(e.id() == ID_side_effect && e.get(ID_statement) == ID_temporary_object)
    {
      // N5008 [expr.type.conv]/2, [class.temporary]: `return T(args)' -- a
      // temporary constructed from arguments that may name tracked variables
      // (`sv(p + pos, len)' in string_view::substr): evaluate the arguments
      // of the initializing constructor call, then the temporary
      exprt temporary = e;
      irept &init = temporary.add(ID_initializer);
      if(
        init.id() == ID_code &&
        to_code(static_cast<exprt &>(init)).get_statement() == ID_expression &&
        static_cast<exprt &>(init).operands().size() == 1)
      {
        exprt &call = static_cast<exprt &>(init).operands().front();
        if(
          call.id() == ID_side_effect &&
          call.get(ID_statement) == ID_function_call)
        {
          auto &args = to_side_effect_expr_function_call(call).arguments();
          for(std::size_t i = 1; i < args.size(); ++i) // 0: &new_object
          {
            // a pointer into a constant array (`&"..."[0]') is a value as
            // it stands; evaluating it would read the element
            if(!array_pointer(args[i], symbol_table).has_value())
              args[i] = eval(args[i]);
          }
        }
      }
      for(auto &op : temporary.operands())
        op = eval(op);
      exprt evaluated = evaluate_temporary_object(
        temporary, symbol_table, ns, ensure_definition);
      if(evaluated.is_not_nil())
        return evaluated;
      // not evaluable here: left as it is, as before (an unused tag object
      // argument such as `__is_move_insertable<_Alloc>{}' must not fail the
      // whole evaluation)
      return e;
    }
    if(e.id() == ID_side_effect && e.get(ID_statement) == ID_function_call)
    {
      // N5008 [meta.const.eval]/1: within a constant evaluation,
      // is_constant_evaluated() is true (libstdc++'s char_traits::length
      // takes its constexpr loop on it)
      const exprt &callee = to_side_effect_expr_function_call(e).function();
      if(
        callee.id() == ID_symbol &&
        has_prefix(
          id2string(to_symbol_expr(callee).get_identifier()),
          "__builtin_is_constant_evaluated"))
      {
        return typecast_exprt::conditional_cast(true_exprt{}, e.type());
      }
      // Recursively evaluate nested function calls (their ARGUMENTS
      // evaluated first, so a call on tracked variables folds too)
      exprt call_copy = e;
      for(auto &op : to_side_effect_expr_function_call(call_copy).arguments())
        op = eval(op);
      exprt evaluated =
        try_evaluate_constexpr(call_copy, symbol_table, ns, ensure_definition);
      if(evaluated.is_not_nil())
        return evaluated;
    }
    // Rebuild expression with evaluated operands
    exprt result = e;
    for(auto &op : result.operands())
      op = eval(op);
    // the implicit dereference of a reference-returning call: the call's
    // value is the referenced object itself (try_evaluate_constexpr unwraps
    // `&constant'), or its address
    if(
      result.id() == ID_dereference && result.operands().size() == 1 &&
      e.get_bool(ID_C_implicit) &&
      to_dereference_expr(e).pointer().id() == ID_side_effect)
    {
      const exprt &value = to_dereference_expr(result).pointer();
      if(value.type().id() != ID_pointer && is_constant_value(value))
        return value;
      if(
        value.id() == ID_address_of &&
        is_constant_value(to_address_of_expr(value).object()))
      {
        return to_address_of_expr(value).object();
      }
    }
    // N5008 [expr.add]/4: pointer +/- integer on a tracked array pointer;
    // [expr.eq]/3, [expr.rel]/4: two pointers into the same array compare
    // by element index
    if(
      (result.id() == ID_plus || result.id() == ID_minus) &&
      result.operands().size() == 2 && result.type().id() == ID_pointer)
    {
      const auto ap = array_pointer(result.operands()[0], symbol_table);
      const exprt &offset = result.operands()[1];
      if(ap && offset.is_constant())
      {
        if(const auto n = numeric_cast<mp_integer>(to_constant_expr(offset)))
        {
          array_pointert moved = *ap;
          moved.index += result.id() == ID_plus ? *n : -*n;
          return make_array_pointer(moved, result.type());
        }
      }
    }
    if(
      (result.id() == ID_equal || result.id() == ID_notequal ||
       result.id() == ID_lt || result.id() == ID_le || result.id() == ID_gt ||
       result.id() == ID_ge) &&
      result.operands().size() == 2)
    {
      const auto lhs = array_pointer(result.operands()[0], symbol_table);
      const auto rhs = array_pointer(result.operands()[1], symbol_table);
      if(lhs && rhs && lhs->array == rhs->array)
      {
        const mp_integer &l = lhs->index, &r = rhs->index;
        const bool v = result.id() == ID_equal      ? l == r
                       : result.id() == ID_notequal ? l != r
                       : result.id() == ID_lt       ? l < r
                       : result.id() == ID_le       ? l <= r
                       : result.id() == ID_gt       ? l > r
                                                    : l >= r;
        return v ? static_cast<exprt>(true_exprt())
                 : static_cast<exprt>(false_exprt());
      }
    }
    if(result.id() == ID_minus && result.operands().size() == 2)
    {
      // pointer difference ([expr.add]/5)
      const auto lhs = array_pointer(result.operands()[0], symbol_table);
      const auto rhs = array_pointer(result.operands()[1], symbol_table);
      if(lhs && rhs && lhs->array == rhs->array)
        return from_integer(lhs->index - rhs->index, result.type());
    }
    // Try to simplify
    simplify(result, ns);
    return result;
  }

  std::optional<exprt> execute(const codet &code, int depth)
  {
    if(depth > 100)
    {
      failed = true;
      return std::nullopt;
    }

    if(code.get_statement() == ID_return)
    {
      if(code.operands().size() == 1)
        return eval(code.op0());
      return std::nullopt;
    }
    if(code.get_statement() == ID_block)
    {
      for(const auto &stmt : code.operands())
      {
        if(stmt.id() != ID_code)
          continue;
        auto r = execute(to_code(stmt), depth + 1);
        if(r.has_value() || failed)
          return r;
      }
      return std::nullopt;
    }
    if(code.get_statement() == ID_ifthenelse)
    {
      exprt cond = eval(code.op0());
      if(cond.is_true() && code.operands()[1].id() == ID_code)
        return execute(to_code(code.operands()[1]), depth + 1);
      if(
        cond.is_false() && code.operands().size() > 2 &&
        code.operands()[2].id() == ID_code)
        return execute(to_code(code.operands()[2]), depth + 1);
      if(cond.is_false())
        return std::nullopt;
      failed = true;
      return std::nullopt;
    }
    if(code.get_statement() == ID_while)
    {
      for(int iter = 0; iter < max_loop_iterations; ++iter)
      {
        exprt cond = eval(code.op0());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true() || code.operands()[1].id() != ID_code)
        {
          failed = true;
          return std::nullopt;
        }
        auto r = execute(to_code(code.operands()[1]), depth + 1);
        if(r.has_value() || failed)
          return r;
      }
      failed = true;
      return std::nullopt;
    }
    if(code.get_statement() == ID_dowhile)
    {
      // C++ [stmt.dowhile]: the body is executed BEFORE the condition is
      // evaluated.  Needed for e.g. libstdc++ chrono duration's constexpr
      // `_S_gcd`, whose do-while body computes the gcd used in the
      // `__divide` member alias's default template arguments; without it
      // the constant evaluation gave up and the __is_harmonic constraint
      // degraded to false.
      for(int iter = 0; iter < max_loop_iterations; ++iter)
      {
        if(code.operands()[1].id() != ID_code)
        {
          failed = true;
          return std::nullopt;
        }
        auto r = execute(to_code(code.operands()[1]), depth + 1);
        if(r.has_value() || failed)
          return r;
        exprt cond = eval(code.op0());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true())
        {
          failed = true;
          return std::nullopt;
        }
      }
      failed = true;
      return std::nullopt;
    }
    if(code.get_statement() == ID_for)
    {
      // N5008 [stmt.for]: init-statement once, then while the condition
      // holds: body, then the iteration expression.  The C++ front end
      // hoists a declared loop variable into an enclosing block, so the
      // init slot is usually empty here.  The loop of libstdc++'s
      // __find_uniq_type_in_pack (std::variant's __exactly_once) is the
      // motivating shape; without it the evaluation gave up and the
      // converting constructor's constraint silently failed.
      const auto &for_code = to_code_for(code);
      if(for_code.init().id() == ID_code)
      {
        auto r = execute(to_code(for_code.init()), depth + 1);
        if(r.has_value() || failed)
          return r;
      }
      for(int iter = 0; iter < max_loop_iterations; ++iter)
      {
        exprt cond = eval(for_code.cond());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true() || for_code.body().id() != ID_code)
        {
          failed = true;
          return std::nullopt;
        }
        auto r = execute(to_code(for_code.body()), depth + 1);
        if(r.has_value() || failed)
          return r;
        if(for_code.iter().id() == ID_code)
        {
          auto ri = execute(to_code(for_code.iter()), depth + 1);
          if(ri.has_value() || failed)
            return ri;
        }
        else if(!apply_side_effect(for_code.iter()))
        {
          failed = true;
          return std::nullopt;
        }
      }
      failed = true;
      return std::nullopt;
    }
    if(code.get_statement() == ID_assign)
    {
      const auto &lhs = code.op0();
      if(this_member_index(lhs))
      {
        side_effect_exprt as_effect{
          ID_assign, lhs.type(), code.source_location()};
        as_effect.add_to_operands(exprt{lhs}, exprt{code.op1()});
        if(!apply_side_effect(as_effect))
          failed = true;
        return std::nullopt;
      }
      exprt rhs = eval_initializer(code.op1());
      if(lhs.id() == ID_symbol && is_trackable(rhs))
        vars[to_symbol_expr(lhs).get_identifier()] = rhs;
      else
        failed = true;
      return std::nullopt;
    }
    if(code.get_statement() == ID_decl_block)
    {
      for(const auto &stmt : code.operands())
      {
        if(stmt.id() != ID_code)
          continue;
        auto r = execute(to_code(stmt), depth + 1);
        if(r.has_value() || failed)
          return r;
      }
      return std::nullopt;
    }
    if(code.get_statement() == ID_decl)
    {
      // Variable declaration: bind the declared variable to its
      // initializer's VALUE when one is present ([dcl.init]); only
      // default-initialize to zero when there is none.  Dropping the
      // initializer made e.g. the loop-local remainder in chrono
      // duration's constexpr _S_gcd start at zero, corrupting the gcd.
      if(code.operands().size() > 0 && code.op0().id() == ID_symbol)
      {
        const auto &sym = to_symbol_expr(code.op0());
        if(code.operands().size() >= 2)
        {
          exprt init = eval_initializer(code.op1());
          if(!is_trackable(init))
          {
            failed = true;
            return std::nullopt;
          }
          vars[sym.get_identifier()] = init;
        }
        else if(sym.type().id() == ID_array || sym.type().id() == ID_struct_tag)
        {
          failed = true;
          return std::nullopt;
        }
        else
          vars[sym.get_identifier()] = from_integer(0, sym.type());
      }
      return std::nullopt;
    }
    if(code.get_statement() == ID_expression)
    {
      // An expression statement may BE an assignment
      // (`side_effect statement=assign`), e.g. the `__m = __n; __n = __rem;`
      // steps of chrono duration's constexpr _S_gcd do-while body, or a
      // compound assignment / increment (`__n = __i`, `++__i`).  Apply it to
      // the tracked variables; skipping it froze the loop variables, so the
      // termination condition never changed and evaluation gave up.
      if(!code.operands().empty() && !apply_side_effect(code.op0()))
        failed = true;
      return std::nullopt;
    }
    if(code.get_statement() == ID_skip)
      return std::nullopt;

    failed = true;
    return std::nullopt;
  }
};

exprt try_evaluate_constexpr(
  const exprt &expr,
  const symbol_table_baset &symbol_table,
  const namespacet &ns,
  const std::function<bool(const irep_idt &)> &ensure_definition)
{
  if(expr.id() != ID_side_effect)
    return nil_exprt();
  // N5008 [expr.const]/5, [class.temporary]: a temporary of literal class
  // type initialised by a constexpr constructor (`Fixed(42)`, `Fixed{42}`
  // as a class-type template argument, [temp.arg.nontype]/1) -- evaluate
  // the constructor call the temporary's initializer holds; its result is
  // the object's value.
  if(expr.get(ID_statement) == ID_temporary_object)
    return evaluate_temporary_object(expr, symbol_table, ns, ensure_definition);
  if(expr.get(ID_statement) != ID_function_call)
    return nil_exprt();

  const auto &call = to_side_effect_expr_function_call(expr);
  const auto &function = call.function();
  const auto &arguments = call.arguments();

  // N5008 [expr.const]: every argument must be a constant expression --
  // here, an expression tree without symbol references (a scalar constant,
  // an aggregate of constants such as a `constexpr` object of class type, or
  // the address of a temporary holding one, for a reference parameter).
  // A constructor call's object operand is the address of the object under
  // construction (`&new_object` for a temporary); the constructor is
  // evaluated on a zero-initialised value of the class ([dcl.init.general]
  // for the members not named by a mem-initializer, see below).  A member
  // function call's object operand may be the address of a constexpr object
  // -- a const symbol whose value is a struct constant ([dcl.constexpr]/6,
  // `constexpr S s; s.n()`) -- or of a struct constant; `this` is then bound
  // to that value ([expr.const]: reading a member of such an object is a
  // core constant expression).
  const auto &func_type_probe =
    function.id() == ID_symbol && function.type().id() == ID_code
      ? to_code_type(function.type())
      : code_typet{{}, empty_typet{}};
  const bool is_constructor =
    func_type_probe.return_type().id() == ID_constructor;
  typet constructed_type;
  exprt this_object_value = nil_exprt();
  if(is_constructor)
  {
    if(
      arguments.empty() || arguments.front().id() != ID_address_of ||
      to_address_of_expr(arguments.front()).object().id() != ID_new_object)
    {
      return nil_exprt();
    }
    constructed_type = to_address_of_expr(arguments.front()).object().type();
    if(constructed_type.id() != ID_struct_tag)
      return nil_exprt();
  }
  else
  {
    // a member function call on a constexpr object: bind `this' to its value
    this_object_value =
      constexpr_this_object_value(func_type_probe, arguments, symbol_table);
    if(this_object_value.is_not_nil())
    {
      constructed_type = this_object_value.type();
      if(constructed_type.id() != ID_struct_tag)
        return nil_exprt();
    }
  }

  // N5008 [expr.const]: every argument must be a constant expression --
  // here, an expression tree without symbol references (a scalar constant,
  // an aggregate of constants such as a `constexpr` object of class type, or
  // the address of a temporary holding one, for a reference parameter) --
  // apart from the object operand handled above.
  for(std::size_t i = 0; i < arguments.size(); ++i)
  {
    if(i == 0 && (is_constructor || this_object_value.is_not_nil()))
      continue;
    if(!is_constexpr_call_argument(arguments[i], symbol_table))
      return nil_exprt();
  }

  // Look up the function body
  if(function.id() != ID_symbol)
    return nil_exprt();
  const irep_idt &func_id = to_symbol_expr(function).get_identifier();
  const symbolt *func_sym = symbol_table.lookup(func_id);
  if(func_sym == nullptr)
    return nil_exprt();
  // N5008 [temp.inst]/5: a definition still in the deferred queue (its
  // parsed body carries no code type yet) is instantiated on demand
  if(func_sym->value.type().id() != ID_code)
  {
    if(!ensure_definition || !ensure_definition(func_id))
      return nil_exprt();
    func_sym = symbol_table.lookup(func_id);
    if(func_sym == nullptr)
      return nil_exprt();
  }
  if(func_sym->value.is_nil())
    return nil_exprt();

  const auto &body = func_sym->value;
  if(body.id() != ID_code || body.type().id() != ID_code)
    return nil_exprt();
  // N5008 [implimits]: recursive constexpr function invocations [512];
  // the depth guard also stops a runaway evaluation.
  static int eval_depth = 0;
  if(eval_depth > 512)
    return nil_exprt();
  ++eval_depth;
  struct depth_guardt
  {
    ~depth_guardt()
    {
      --eval_depth;
    }
  } dg;

  // Get parameter names
  const auto &func_type = to_code_type(func_sym->type);
  const auto &params = func_type.parameters();
  if(params.size() != arguments.size())
    return nil_exprt();

  // Build a variable map: parameter → constant value
  // For reference parameters, unwrap address_of and temporaries.
  std::map<irep_idt, exprt> vars;
  irep_idt this_id;
  if(is_constructor)
  {
    // `this` denotes the object under construction; its VALUE (a struct
    // constant) is tracked under the `this` parameter's identifier and
    // updated by the mem-initializer / body assignments `this->m = ...`.
    this_id = params.front().get_identifier();
    const auto zero = itanium_abi_cpp_zero_initializer(
      constructed_type, source_locationt{}, ns);
    if(!zero.has_value() || zero->id() != ID_struct)
      return nil_exprt();
    vars[this_id] = *zero;
  }
  else if(this_object_value.is_not_nil())
  {
    // a member function on a constexpr object: `this' denotes that object
    this_id = params.front().get_identifier();
    vars[this_id] = this_object_value;
  }
  const bool skip_this_argument =
    is_constructor || this_object_value.is_not_nil();
  for(std::size_t i = skip_this_argument ? 1 : 0; i < params.size(); ++i)
  {
    if(arguments[i].id() == ID_address_of)
    {
      const auto &obj = to_address_of_expr(arguments[i]).object();
      if(obj.is_constant())
        vars[params[i].get_identifier()] = obj;
      else if(
        obj.id() == ID_side_effect && obj.operands().size() == 1 &&
        obj.operands()[0].is_constant())
        vars[params[i].get_identifier()] = obj.operands()[0];
      else
      {
        // `&"ab"[(int)1]': fold the index so that the pointer is tracked as
        // a pointer into the array (array_pointer)
        // (only the index: the simplifier rewrites the whole address to
        // `&"ab"[0] + 1')
        exprt argument = arguments[i];
        exprt &object = to_address_of_expr(argument).object();
        if(object.id() == ID_index)
          simplify(to_index_expr(object).index(), ns);
        vars[params[i].get_identifier()] = std::move(argument);
      }
    }
    else
    {
      // N5008 [conv.integral], [expr.const]: an argument converted to the
      // parameter type (`id(7)' with `unsigned long' parameter arrives as
      // `(unsigned long)7') is folded to the constant it denotes; unfolded,
      // `return r' would not yield a constant.
      exprt argument = arguments[i];
      simplify(argument, ns);
      vars[params[i].get_identifier()] = std::move(argument);
    }
  }

  constexpr_interpretert interpreter{
    symbol_table, ns, ensure_definition, constructed_type};
  interpreter.vars = std::move(vars);
  interpreter.this_id = this_id;

  auto result = interpreter.execute(to_code(body), 0);
  if(interpreter.failed)
    return nil_exprt();
  if(is_constructor)
  {
    // the constructor's result is the constructed object; a `return;` (or
    // falling off the end) leaves the tracked value as it is
    const exprt &obj = interpreter.vars.at(this_id);
    return constexpr_interpretert::is_constant_value(obj, symbol_table)
             ? obj
             : static_cast<exprt>(nil_exprt());
  }
  if(result.has_value())
  {
    if(result->is_constant())
      return *result;
    // a class prvalue ([expr.const]/14: a constant expression of class type
    // whose members are constants), `return P{1, 2};' or a string_view built
    // by a consteval function (GCC 16's _Escapes<_CharT>::_S_tab())
    if(
      result->id() == ID_struct &&
      constexpr_interpretert::is_constant_value(*result, symbol_table))
    {
      return *result;
    }
    // a pointer into a constant array ([expr.const]/11: the address of an
    // element of a static object; initializer_list::begin())
    if(array_pointer(*result, symbol_table))
      return *result;
    // Reference-returning functions (like std::max) return
    // address_of(constant).  Unwrap to the constant.
    if(
      result->id() == ID_address_of &&
      to_address_of_expr(*result).object().is_constant())
    {
      return to_address_of_expr(*result).object();
    }
  }

  return nil_exprt();
}
