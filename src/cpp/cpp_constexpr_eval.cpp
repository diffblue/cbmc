/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// Constant evaluation of constexpr function calls (N5008 [expr.const])

#include "cpp_constexpr_eval.h"

#include <util/arith_tools.h>
#include <util/expr_initializer.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

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
  const auto zero = zero_initializer(expr.type(), source_locationt{}, ns);
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
      const std::size_t index =
        object_type.component_number(to_member_expr(lhs).get_component_name());
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
    bool has_symbol = false;
    arguments[i].visit_pre(
      [&has_symbol](const exprt &e)
      {
        if(e.id() == ID_symbol)
          has_symbol = true;
      });
    if(has_symbol)
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
    const auto zero =
      zero_initializer(constructed_type, source_locationt{}, ns);
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
        vars[params[i].get_identifier()] = arguments[i];
    }
    else
      vars[params[i].get_identifier()] = arguments[i];
  }

  // N5008 [implimits] recommends 1 048 576 full-expression evaluations in a
  // core constant expression; loops are bounded well below that -- an
  // evaluation that needs more is left to run time.
  const int max_loop_iterations = 4096;

  // Mini-interpreter: execute the body with bounded iterations
  std::function<std::optional<exprt>(const codet &, int)> execute;
  std::function<exprt(const exprt &)> eval;

  // A tracked value: a scalar constant, or an aggregate of constants (the
  // `constexpr bool found[] = {__is_same(T, Ts)...}` local of libstdc++'s
  // __find_uniq_type_in_pack, read back through `found[i]`).
  auto is_constant_value = [](const exprt &e) -> bool
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
  };

  // Apply an assignment-like side effect (`=`, compound assignment,
  // `++`/`--`) to a tracked variable.  Returns false when the effect cannot
  // be tracked (the caller then gives up on the evaluation).
  // `this->m` -- the object under construction is tracked by value, so a
  // member access through `this` reads the tracked struct's component.
  auto this_member_index = [&](const exprt &e) -> std::optional<std::size_t>
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
    return st.component_number(to_member_expr(e).get_component_name());
  };

  auto apply_side_effect = [&](const exprt &e) -> bool
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
        if(!is_constant_value(rhs))
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
    if(e.operands().empty() || e.operands()[0].id() != ID_symbol)
      return false;
    const irep_idt var = to_symbol_expr(e.operands()[0]).get_identifier();
    if(st == ID_assign)
    {
      if(e.operands().size() != 2)
        return false;
      exprt rhs = eval(e.operands()[1]);
      if(!is_constant_value(rhs))
        return false;
      vars[var] = rhs;
      return true;
    }
    const auto cur = vars.find(var);
    if(cur == vars.end() || !cur->second.is_constant())
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
  };

  eval = [&](const exprt &e) -> exprt
  {
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
        return it->second;
      // a `constexpr` variable (a static data member `value`, an
      // enumerator) is a macro whose initializer is its value
      const symbolt *var_sym =
        symbol_table.lookup(to_symbol_expr(e).get_identifier());
      if(
        var_sym != nullptr && var_sym->is_macro && !var_sym->is_type &&
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
    if(e.id() == ID_side_effect && e.get(ID_statement) == ID_function_call)
    {
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
    // Try to simplify
    simplify(result, ns);
    return result;
  };

  execute = [&](const codet &code, int depth) -> std::optional<exprt>
  {
    if(depth > 100)
      return std::nullopt;

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
        if(r.has_value())
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
      return std::nullopt; // can't evaluate condition
    }
    if(code.get_statement() == ID_while)
    {
      for(int iter = 0; iter < max_loop_iterations; ++iter)
      {
        exprt cond = eval(code.op0());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true())
          return std::nullopt; // can't evaluate condition
        if(code.operands()[1].id() != ID_code)
          return std::nullopt;
        auto r = execute(to_code(code.operands()[1]), depth + 1);
        if(r.has_value())
          return r;
      }
      return std::nullopt; // too many iterations
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
          return std::nullopt;
        auto r = execute(to_code(code.operands()[1]), depth + 1);
        if(r.has_value())
          return r;
        exprt cond = eval(code.op0());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true())
          return std::nullopt; // can't evaluate condition
      }
      return std::nullopt; // too many iterations
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
        if(r.has_value())
          return r;
      }
      for(int iter = 0; iter < max_loop_iterations; ++iter)
      {
        exprt cond = eval(for_code.cond());
        if(cond.is_false())
          return std::nullopt; // loop done, no return
        if(!cond.is_true())
          return std::nullopt; // can't evaluate condition
        if(for_code.body().id() != ID_code)
          return std::nullopt;
        auto r = execute(to_code(for_code.body()), depth + 1);
        if(r.has_value())
          return r;
        if(for_code.iter().id() == ID_code)
        {
          auto ri = execute(to_code(for_code.iter()), depth + 1);
          if(ri.has_value())
            return ri;
        }
        else if(!apply_side_effect(for_code.iter()))
          return std::nullopt;
      }
      return std::nullopt; // too many iterations
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
          return std::nullopt;
        return std::nullopt;
      }
      exprt rhs = eval(code.op1());
      if(lhs.id() == ID_symbol)
        vars[to_symbol_expr(lhs).get_identifier()] = rhs;
      return std::nullopt;
    }
    if(code.get_statement() == ID_decl_block)
    {
      for(const auto &stmt : code.operands())
      {
        if(stmt.id() != ID_code)
          continue;
        auto r = execute(to_code(stmt), depth + 1);
        if(r.has_value())
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
          exprt init = eval(code.op1());
          if(!is_constant_value(init))
            return std::nullopt; // can't track this variable's value
          vars[sym.get_identifier()] = init;
        }
        else if(sym.type().id() == ID_array || sym.type().id() == ID_struct_tag)
          return std::nullopt; // an aggregate without initializer: untracked
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
        return std::nullopt; // lost track of a variable's value
      return std::nullopt;
    }
    if(code.get_statement() == ID_skip)
      return std::nullopt;

    return std::nullopt; // unknown statement
  };

  auto result = execute(to_code(body), 0);
  if(is_constructor)
  {
    // the constructor's result is the constructed object; a `return;` (or
    // falling off the end) leaves the tracked value as it is
    const exprt &obj = vars.at(this_id);
    return is_constant_value(obj) ? obj : static_cast<exprt>(nil_exprt());
  }
  if(result.has_value())
  {
    if(result->is_constant())
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
