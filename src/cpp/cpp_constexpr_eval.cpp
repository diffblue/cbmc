/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// Constant evaluation of constexpr function calls (N5008 [expr.const])

#include "cpp_constexpr_eval.h"

#include <util/arith_tools.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include <map>
#include <optional>

exprt try_evaluate_constexpr(
  const exprt &expr,
  const symbol_table_baset &symbol_table,
  const namespacet &ns,
  const std::function<bool(const irep_idt &)> &ensure_definition)
{
  if(expr.id() != ID_side_effect)
    return nil_exprt();
  if(expr.get(ID_statement) != ID_function_call)
    return nil_exprt();

  const auto &call = to_side_effect_expr_function_call(expr);
  const auto &function = call.function();
  const auto &arguments = call.arguments();

  // N5008 [expr.const]: every argument must be a constant expression --
  // here, an expression tree without symbol references (a scalar constant,
  // an aggregate of constants such as a `constexpr` object of class type, or
  // the address of a temporary holding one, for a reference parameter).
  for(const auto &arg : arguments)
  {
    bool has_symbol = false;
    arg.visit_pre(
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
  for(std::size_t i = 0; i < params.size(); ++i)
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
  auto apply_side_effect = [&](const exprt &e) -> bool
  {
    if(e.id() != ID_side_effect)
      return true; // no effect to apply (e.g. a plain expression)
    const irep_idt &st = e.get(ID_statement);
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
