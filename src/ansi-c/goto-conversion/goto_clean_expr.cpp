/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol.h>

#include "destructor.h"

symbol_exprt goto_convertt::make_compound_literal(
  const exprt &expr,
  goto_programt &dest,
  const irep_idt &mode)
{
  const source_locationt source_location = expr.find_source_location();

  symbolt &new_symbol = get_fresh_aux_symbol(
    expr.type(),
    tmp_symbol_prefix,
    "literal",
    source_location,
    mode,
    symbol_table);
  new_symbol.is_static_lifetime = lifetime != lifetimet::AUTOMATIC_LOCAL;
  new_symbol.value = expr;

  // The value might depend on a variable, thus
  // generate code for this.

  symbol_exprt result = new_symbol.symbol_expr();
  result.add_source_location() = source_location;

  // The lifetime of compound literals is really that of
  // the block they are in.
  if(!new_symbol.is_static_lifetime)
    copy(code_declt(result), DECL, dest);

  code_assignt code_assign(result, expr);
  code_assign.add_source_location() = source_location;
  convert(code_assign, dest, mode);

  // now create a 'dead' instruction
  if(!new_symbol.is_static_lifetime)
  {
    code_deadt code_dead(result);
    targets.scope_stack.add(std::move(code_dead), {});
  }

  return result;
}

/// Returns 'true' for expressions that may change the program
/// state.
/// Expressions that may trigger undefined behavior
/// (e.g., dereference, index, division) are deliberately not
/// included.
bool goto_convertt::needs_cleaning(const exprt &expr)
{
  if(
    expr.id() == ID_side_effect || expr.id() == ID_compound_literal ||
    expr.id() == ID_comma)
  {
    return true;
  }

  // We can't flatten quantified expressions by introducing new literals for
  // conditional expressions.  This is because the body of the quantified
  // may refer to bound variables, which are not visible outside the scope
  // of the quantifier.
  //
  // For example, the following transformation would not be valid:
  //
  // forall (i : int) (i == 0 || i > 10)
  //
  //   transforming to
  //
  // g1 = (i == 0)
  // g2 = (i > 10)
  // forall (i : int) (g1 || g2)
  if(expr.id() == ID_forall || expr.id() == ID_exists)
    return false;

  for(const auto &op : expr.operands())
  {
    if(needs_cleaning(op))
      return true;
  }

  return false;
}

/// re-write boolean operators into ?:
void goto_convertt::rewrite_boolean(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies);
  PRECONDITION_WITH_DIAGNOSTICS(
    expr.is_boolean(),
    expr.find_source_location(),
    "'",
    expr.id(),
    "' must be Boolean, but got ",
    irep_pretty_diagnosticst{expr});

  const source_locationt source_location = expr.find_source_location();

  // re-write "a ==> b" into a?b:1
  if(auto implies = expr_try_dynamic_cast<implies_exprt>(expr))
  {
    expr = if_exprt{
      std::move(implies->lhs()),
      std::move(implies->rhs()),
      true_exprt{}.with_source_location(source_location),
      bool_typet{}};
    return;
  }

  // re-write "a && b" into nested a?b:0
  // re-write "a || b" into nested a?1:b

  exprt tmp;

  if(expr.id() == ID_and)
    tmp = true_exprt();
  else // ID_or
    tmp = false_exprt();

  tmp.add_source_location() = source_location;

  exprt::operandst &ops = expr.operands();

  // start with last one
  for(exprt::operandst::reverse_iterator it = ops.rbegin(); it != ops.rend();
      ++it)
  {
    exprt &op = *it;

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      op.is_boolean(),
      "boolean operators must have only boolean operands",
      source_location);

    if(expr.id() == ID_and)
    {
      exprt if_e =
        if_exprt{op, tmp, false_exprt{}.with_source_location(source_location)}
          .with_source_location(source_location);
      tmp.swap(if_e);
      continue;
    }
    if(expr.id() == ID_or)
    {
      exprt if_e =
        if_exprt{op, true_exprt{}.with_source_location(source_location), tmp}
          .with_source_location(source_location);
      tmp.swap(if_e);
      continue;
    }
    UNREACHABLE;
  }

  expr.swap(tmp);
}

goto_convertt::clean_expr_resultt goto_convertt::clean_expr(
  exprt &expr,
  const irep_idt &mode,
  bool result_is_used)
{
  // this cleans:
  //   && || ==> ?: comma (control-dependency)
  //   function calls
  //   object constructors like arrays, string constants, structs
  //   ++ -- (pre and post)
  //   compound assignments
  //   compound literals

  if(!needs_cleaning(expr))
    return {};

  if(expr.id() == ID_and || expr.id() == ID_or || expr.id() == ID_implies)
  {
    // rewrite into ?:
    rewrite_boolean(expr);

    // recursive call
    return clean_expr(expr, mode, result_is_used);
  }
  else if(expr.id() == ID_if)
  {
    // first clean condition
    clean_expr_resultt side_effects =
      clean_expr(to_if_expr(expr).cond(), mode, true);

    // possibly done now
    if(
      !needs_cleaning(to_if_expr(expr).true_case()) &&
      !needs_cleaning(to_if_expr(expr).false_case()))
    {
      return side_effects;
    }

    // copy expression
    if_exprt if_expr = to_if_expr(expr);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      if_expr.cond().is_boolean(),
      "condition for an 'if' must be boolean",
      if_expr.find_source_location());

    const source_locationt source_location = expr.find_source_location();

#if 0
    // We do some constant-folding here, to mimic
    // what typical compilers do.
    {
      exprt tmp_cond=if_expr.cond();
      simplify(tmp_cond, ns);
      if(tmp_cond.is_true())
      {
        clean_expr(if_expr.true_case(), dest, result_is_used);
        expr=if_expr.true_case();
        return;
      }
      else if(tmp_cond.is_false())
      {
        clean_expr(if_expr.false_case(), dest, result_is_used);
        expr=if_expr.false_case();
        return;
      }
    }
#endif

    clean_expr_resultt tmp_true(
      clean_expr(if_expr.true_case(), mode, result_is_used));

    clean_expr_resultt tmp_false(
      clean_expr(if_expr.false_case(), mode, result_is_used));

    if(result_is_used)
    {
      symbolt &new_symbol = new_tmp_symbol(
        expr.type(),
        "if_expr",
        side_effects.side_effects,
        source_location,
        mode);

      code_assignt assignment_true;
      assignment_true.lhs() = new_symbol.symbol_expr();
      assignment_true.rhs() = if_expr.true_case();
      assignment_true.add_source_location() = source_location;
      convert(assignment_true, tmp_true.side_effects, mode);

      code_assignt assignment_false;
      assignment_false.lhs() = new_symbol.symbol_expr();
      assignment_false.rhs() = if_expr.false_case();
      assignment_false.add_source_location() = source_location;
      convert(assignment_false, tmp_false.side_effects, mode);

      // overwrites expr
      expr = new_symbol.symbol_expr();
    }
    else
    {
      // preserve the expressions for possible later checks
      if(if_expr.true_case().is_not_nil())
      {
        // add a (void) type cast so that is_skip catches it in case the
        // expression is just a constant
        code_expressiont code_expression(
          typecast_exprt(if_expr.true_case(), empty_typet()));
        convert(code_expression, tmp_true.side_effects, mode);
      }

      if(if_expr.false_case().is_not_nil())
      {
        // add a (void) type cast so that is_skip catches it in case the
        // expression is just a constant
        code_expressiont code_expression(
          typecast_exprt(if_expr.false_case(), empty_typet()));
        convert(code_expression, tmp_false.side_effects, mode);
      }

      expr = nil_exprt();
    }

    // generate guard for argument side-effects
    generate_ifthenelse(
      if_expr.cond(),
      source_location,
      tmp_true.side_effects,
      if_expr.true_case().source_location(),
      tmp_false.side_effects,
      if_expr.false_case().source_location(),
      side_effects.side_effects,
      mode);

    destruct_locals(tmp_false.temporaries, side_effects.side_effects, ns);
    destruct_locals(tmp_true.temporaries, side_effects.side_effects, ns);
    destruct_locals(side_effects.temporaries, side_effects.side_effects, ns);
    side_effects.temporaries.clear();

    if(expr.is_not_nil())
      side_effects.add_temporary(to_symbol_expr(expr).get_identifier());

    return side_effects;
  }
  else if(expr.id() == ID_comma)
  {
    clean_expr_resultt side_effects;

    if(result_is_used)
    {
      exprt result;

      Forall_operands(it, expr)
      {
        bool last = (it == --expr.operands().end());

        // special treatment for last one
        if(last)
        {
          result.swap(*it);
          side_effects.add(clean_expr(result, mode, true));
        }
        else
        {
          side_effects.add(clean_expr(*it, mode, false));

          // remember these for later checks
          if(it->is_not_nil())
            convert(code_expressiont(*it), side_effects.side_effects, mode);
        }
      }

      expr.swap(result);
    }
    else // result not used
    {
      Forall_operands(it, expr)
      {
        side_effects.add(clean_expr(*it, mode, false));

        // remember as expression statement for later checks
        if(it->is_not_nil())
          convert(code_expressiont(*it), side_effects.side_effects, mode);
      }

      expr = nil_exprt();
    }

    return side_effects;
  }
  else if(expr.id() == ID_typecast)
  {
    typecast_exprt &typecast = to_typecast_expr(expr);

    // preserve 'result_is_used'
    clean_expr_resultt side_effects =
      clean_expr(typecast.op(), mode, result_is_used);

    if(typecast.op().is_nil())
      expr.make_nil();

    return side_effects;
  }
  else if(expr.id() == ID_side_effect)
  {
    // some of the side-effects need special treatment!
    const irep_idt statement = to_side_effect_expr(expr).get_statement();

    if(statement == ID_gcc_conditional_expression)
    {
      // need to do separately
      return remove_gcc_conditional_expression(expr, mode);
    }
    else if(statement == ID_statement_expression)
    {
      // need to do separately to prevent that
      // the operands of expr get 'cleaned'
      return remove_statement_expression(
        to_side_effect_expr(expr), mode, result_is_used);
    }
    else if(statement == ID_assign)
    {
      // we do a special treatment for x=f(...)
      INVARIANT(
        expr.operands().size() == 2,
        "side-effect assignment expressions must have two operands");

      auto &side_effect_assign = to_side_effect_expr_assign(expr);

      if(
        side_effect_assign.rhs().id() == ID_side_effect &&
        to_side_effect_expr(side_effect_assign.rhs()).get_statement() ==
          ID_function_call)
      {
        clean_expr_resultt side_effects =
          clean_expr(side_effect_assign.lhs(), mode);
        exprt lhs = side_effect_assign.lhs();

        const bool must_use_rhs = assignment_lhs_needs_temporary(lhs);
        if(must_use_rhs)
        {
          side_effects.add(remove_function_call(
            to_side_effect_expr_function_call(side_effect_assign.rhs()),
            mode,
            true));
        }

        // turn into code
        exprt new_lhs = skip_typecast(lhs);
        exprt new_rhs = typecast_exprt::conditional_cast(
          side_effect_assign.rhs(), new_lhs.type());
        code_assignt assignment(std::move(new_lhs), new_rhs);
        assignment.add_source_location() = expr.source_location();
        convert_assign(assignment, side_effects.side_effects, mode);

        if(result_is_used)
          expr = must_use_rhs ? new_rhs : lhs;
        else
          expr.make_nil();

        return side_effects;
      }
    }
  }
  else if(expr.id() == ID_forall || expr.id() == ID_exists)
  {
    DATA_INVARIANT(
      !has_subexpr(expr, ID_side_effect),
      "the front-end should check quantified expressions for side-effects");
  }
  else if(expr.id() == ID_address_of)
  {
    address_of_exprt &addr = to_address_of_expr(expr);
    return clean_expr_address_of(addr.object(), mode);
  }

  clean_expr_resultt side_effects;

  // TODO: evaluation order

  Forall_operands(it, expr)
    side_effects.add(clean_expr(*it, mode));

  if(expr.id() == ID_side_effect)
  {
    side_effects.add(remove_side_effect(
      to_side_effect_expr(expr), mode, result_is_used, false));
  }
  else if(expr.id() == ID_compound_literal)
  {
    // This is simply replaced by the literal
    DATA_INVARIANT(
      expr.operands().size() == 1, "ID_compound_literal has a single operand");
    expr = to_unary_expr(expr).op();
  }

  return side_effects;
}

goto_convertt::clean_expr_resultt
goto_convertt::clean_expr_address_of(exprt &expr, const irep_idt &mode)
{
  clean_expr_resultt side_effects;

  // The address of object constructors can be taken,
  // which is re-written into the address of a variable.

  if(expr.id() == ID_compound_literal)
  {
    DATA_INVARIANT(
      expr.operands().size() == 1, "ID_compound_literal has a single operand");
    side_effects.add(clean_expr(to_unary_expr(expr).op(), mode));
    expr = make_compound_literal(
      to_unary_expr(expr).op(), side_effects.side_effects, mode);
  }
  else if(expr.id() == ID_string_constant)
  {
    // Leave for now, but long-term these might become static symbols.
    // LLVM appears to do precisely that.
  }
  else if(expr.id() == ID_index)
  {
    index_exprt &index_expr = to_index_expr(expr);
    side_effects.add(clean_expr_address_of(index_expr.array(), mode));
    side_effects.add(clean_expr(index_expr.index(), mode));
  }
  else if(expr.id() == ID_dereference)
  {
    dereference_exprt &deref_expr = to_dereference_expr(expr);
    side_effects.add(clean_expr(deref_expr.pointer(), mode));
  }
  else if(expr.id() == ID_comma)
  {
    // Yes, one can take the address of a comma expression.
    // Treatment is similar to clean_expr() above.

    exprt result;

    Forall_operands(it, expr)
    {
      bool last = (it == --expr.operands().end());

      // special treatment for last one
      if(last)
        result.swap(*it);
      else
      {
        side_effects.add(clean_expr(*it, mode, false));

        // get any side-effects
        if(it->is_not_nil())
          convert(code_expressiont(*it), side_effects.side_effects, mode);
      }
    }

    expr.swap(result);

    // do again
    side_effects.add(clean_expr_address_of(expr, mode));
  }
  else if(expr.id() == ID_side_effect)
  {
    side_effects.add(
      remove_side_effect(to_side_effect_expr(expr), mode, true, true));
  }
  else
    Forall_operands(it, expr)
      side_effects.add(clean_expr_address_of(*it, mode));

  return side_effects;
}

goto_convertt::clean_expr_resultt
goto_convertt::remove_gcc_conditional_expression(
  exprt &expr,
  const irep_idt &mode)
{
  clean_expr_resultt side_effects;

  {
    auto &binary_expr = to_binary_expr(expr);

    // first remove side-effects from condition
    side_effects = clean_expr(to_binary_expr(expr).op0(), mode);

    // now we can copy op0 safely
    if_exprt if_expr(
      typecast_exprt::conditional_cast(binary_expr.op0(), bool_typet()),
      binary_expr.op0(),
      binary_expr.op1(),
      expr.type());
    if_expr.add_source_location() = expr.source_location();

    expr.swap(if_expr);
  }

  // there might still be junk in expr.op2()
  side_effects.add(clean_expr(expr, mode));

  return side_effects;
}
