/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <util/cprover_prefix.h>
#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>

#include <util/c_types.h>

symbol_exprt goto_convertt::make_compound_literal(
  const exprt &expr,
  goto_programt &dest,
  const irep_idt &mode)
{
  const source_locationt source_location=expr.find_source_location();

  symbolt &new_symbol = get_fresh_aux_symbol(
    expr.type(),
    tmp_symbol_prefix,
    "literal",
    source_location,
    mode,
    symbol_table);
  new_symbol.is_static_lifetime=source_location.get_function().empty();
  new_symbol.value=expr;

  // The value might depend on a variable, thus
  // generate code for this.

  symbol_exprt result=new_symbol.symbol_expr();
  result.add_source_location()=source_location;

  // The lifetime of compound literals is really that of
  // the block they are in.
  copy(code_declt(result), DECL, dest);

  code_assignt code_assign(result, expr);
  code_assign.add_source_location()=source_location;
  convert(code_assign, dest, mode);

  // now create a 'dead' instruction
  if(!new_symbol.is_static_lifetime)
  {
    code_deadt code_dead(result);
    targets.destructor_stack.push_back(code_dead);
  }

  return result;
}

bool goto_convertt::needs_cleaning(const exprt &expr)
{
  if(expr.id()==ID_dereference ||
     expr.id()==ID_side_effect ||
     expr.id()==ID_compound_literal ||
     expr.id()==ID_comma)
    return true;

  if(expr.id()==ID_index)
  {
    // Will usually clean index expressions because of possible
    // memory violation in case of out-of-bounds indices.
    // We do an exception for "string-lit"[0], which is safe.
    if(to_index_expr(expr).array().id()==ID_string_constant &&
       to_index_expr(expr).index().is_zero())
      return false;

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
  if(expr.id()==ID_forall || expr.id()==ID_exists)
    return false;

  forall_operands(it, expr)
    if(needs_cleaning(*it))
      return true;

  return false;
}

/// re-write boolean operators into ?:
void goto_convertt::rewrite_boolean(exprt &expr)
{
  assert(expr.id()==ID_and || expr.id()==ID_or);

  if(!expr.is_boolean())
  {
    error().source_location=expr.find_source_location();
    error() << "`" << expr.id() << "' must be Boolean, but got "
            << expr.pretty() << eom;
    throw 0;
  }

  // re-write "a && b" into nested a?b:0
  // re-write "a || b" into nested a?1:b

  exprt tmp;

  if(expr.id()==ID_and)
    tmp=true_exprt();
  else // ID_or
    tmp=false_exprt();

  exprt::operandst &ops=expr.operands();

  // start with last one
  for(exprt::operandst::reverse_iterator
      it=ops.rbegin();
      it!=ops.rend();
      ++it)
  {
    exprt &op=*it;

    if(!op.is_boolean())
    {
      error().source_location=expr.find_source_location();
      error() << "`" << expr.id() << "' takes Boolean "
              << "operands only, but got " << op.pretty() << eom;
      throw 0;
    }

    if(expr.id()==ID_and)
    {
      if_exprt if_e(op, tmp, false_exprt());
      tmp.swap(if_e);
    }
    else // ID_or
    {
      if_exprt if_e(op, true_exprt(), tmp);
      tmp.swap(if_e);
    }
  }

  expr.swap(tmp);
}

void goto_convertt::clean_expr(
  exprt &expr,
  goto_programt &dest,
  const irep_idt &mode,
  bool result_is_used)
{
  // this cleans:
  //   && || ?: comma (control-dependency)
  //   function calls
  //   object constructors like arrays, string constants, structs
  //   ++ -- (pre and post)
  //   compound assignments
  //   compound literals

  if(!needs_cleaning(expr))
    return;

  if(expr.id()==ID_and || expr.id()==ID_or)
  {
    // rewrite into ?:
    rewrite_boolean(expr);

    // recursive call
    clean_expr(expr, dest, mode, result_is_used);
    return;
  }
  else if(expr.id()==ID_if)
  {
    // first clean condition
    clean_expr(to_if_expr(expr).cond(), dest, mode, true);

    // possibly done now
    if(!needs_cleaning(to_if_expr(expr).true_case()) &&
       !needs_cleaning(to_if_expr(expr).false_case()))
      return;

    // copy expression
    if_exprt if_expr=to_if_expr(expr);

    if(!if_expr.cond().is_boolean())
    {
      error().source_location=if_expr.find_source_location();
      error() << "first argument of `if' must be boolean, but got "
              << if_expr.cond().pretty() << eom;
      throw 0;
    }

    const source_locationt source_location=expr.find_source_location();

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

    goto_programt tmp_true;
    clean_expr(if_expr.true_case(), tmp_true, mode, result_is_used);

    goto_programt tmp_false;
    clean_expr(if_expr.false_case(), tmp_false, mode, result_is_used);

    if(result_is_used)
    {
      symbolt &new_symbol =
        new_tmp_symbol(expr.type(), "if_expr", dest, source_location, mode);

      code_assignt assignment_true;
      assignment_true.lhs()=new_symbol.symbol_expr();
      assignment_true.rhs()=if_expr.true_case();
      assignment_true.add_source_location()=source_location;
      convert(assignment_true, tmp_true, mode);

      code_assignt assignment_false;
      assignment_false.lhs()=new_symbol.symbol_expr();
      assignment_false.rhs()=if_expr.false_case();
      assignment_false.add_source_location()=source_location;
      convert(assignment_false, tmp_false, mode);

      // overwrites expr
      expr=new_symbol.symbol_expr();
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
        convert(code_expression, tmp_true, mode);
      }

      if(if_expr.false_case().is_not_nil())
      {
        // add a (void) type cast so that is_skip catches it in case the
        // expression is just a constant
        code_expressiont code_expression(
          typecast_exprt(if_expr.false_case(), empty_typet()));
        convert(code_expression, tmp_false, mode);
      }

      expr=nil_exprt();
    }

    // generate guard for argument side-effects
    generate_ifthenelse(
      if_expr.cond(), tmp_true, tmp_false, source_location, dest, mode);

    return;
  }
  else if(expr.id()==ID_comma)
  {
    if(result_is_used)
    {
      exprt result;

      Forall_operands(it, expr)
      {
        bool last=(it==--expr.operands().end());

        // special treatment for last one
        if(last)
        {
          result.swap(*it);
          clean_expr(result, dest, mode, true);
        }
        else
        {
          clean_expr(*it, dest, mode, false);

          // remember these for later checks
          if(it->is_not_nil())
            convert(code_expressiont(*it), dest, mode);
        }
      }

      expr.swap(result);
    }
    else // result not used
    {
      Forall_operands(it, expr)
      {
        clean_expr(*it, dest, mode, false);

        // remember as expression statement for later checks
        if(it->is_not_nil())
          convert(code_expressiont(*it), dest, mode);
      }

      expr=nil_exprt();
    }

    return;
  }
  else if(expr.id()==ID_typecast)
  {
    if(expr.operands().size()!=1)
    {
      error().source_location=expr.find_source_location();
      error() << "typecast takes one argument" << eom;
      throw 0;
    }

    // preserve 'result_is_used'
    clean_expr(expr.op0(), dest, mode, result_is_used);

    if(expr.op0().is_nil())
      expr.make_nil();

    return;
  }
  else if(expr.id()==ID_side_effect)
  {
    // some of the side-effects need special treatment!
    const irep_idt statement=to_side_effect_expr(expr).get_statement();

    if(statement==ID_gcc_conditional_expression)
    {
      // need to do separately
      remove_gcc_conditional_expression(expr, dest, mode);
      return;
    }
    else if(statement==ID_statement_expression)
    {
      // need to do separately to prevent that
      // the operands of expr get 'cleaned'
      remove_statement_expression(
        to_side_effect_expr(expr), dest, mode, result_is_used);
      return;
    }
    else if(statement==ID_assign)
    {
      // we do a special treatment for x=f(...)
      assert(expr.operands().size()==2);

      if(expr.op1().id()==ID_side_effect &&
         to_side_effect_expr(expr.op1()).get_statement()==ID_function_call)
      {
        clean_expr(expr.op0(), dest, mode);
        exprt lhs=expr.op0();

        // turn into code
        code_assignt assignment;
        assignment.lhs()=lhs;
        assignment.rhs()=expr.op1();
        assignment.add_source_location()=expr.source_location();
        convert_assign(assignment, dest, mode);

        if(result_is_used)
          expr.swap(lhs);
        else
          expr.make_nil();
        return;
      }
    }
    else if(statement==ID_function_call)
    {
      if(to_side_effect_expr_function_call(expr).function().id()==ID_symbol &&
         to_symbol_expr(
           to_side_effect_expr_function_call(expr).
           function()).get_identifier()=="__noop")
      {
        // __noop needs special treatment, as arguments are not
        // evaluated
        to_side_effect_expr_function_call(expr).arguments().clear();
      }
    }
  }
  else if(expr.id()==ID_forall || expr.id()==ID_exists)
  {
    DATA_INVARIANT(
      !has_subexpr(expr, ID_side_effect),
      "the front-end should check quantified expressions for side-effects");
  }
  else if(expr.id()==ID_address_of)
  {
    assert(expr.operands().size()==1);
    clean_expr_address_of(expr.op0(), dest, mode);
    return;
  }

  // TODO: evaluation order

  Forall_operands(it, expr)
    clean_expr(*it, dest, mode);

  if(expr.id()==ID_side_effect)
  {
    remove_side_effect(to_side_effect_expr(expr), dest, mode, result_is_used);
  }
  else if(expr.id()==ID_compound_literal)
  {
    // This is simply replaced by the literal
    assert(expr.operands().size()==1);
    expr=expr.op0();
  }
}

void goto_convertt::clean_expr_address_of(
  exprt &expr,
  goto_programt &dest,
  const irep_idt &mode)
{
  // The address of object constructors can be taken,
  // which is re-written into the address of a variable.

  if(expr.id()==ID_compound_literal)
  {
    assert(expr.operands().size()==1);
    clean_expr(expr.op0(), dest, mode);
    expr = make_compound_literal(expr.op0(), dest, mode);
  }
  else if(expr.id()==ID_string_constant)
  {
    // Leave for now, but long-term these might become static symbols.
    // LLVM appears to do precisely that.
  }
  else if(expr.id()==ID_index)
  {
    assert(expr.operands().size()==2);
    clean_expr_address_of(expr.op0(), dest, mode);
    clean_expr(expr.op1(), dest, mode);
  }
  else if(expr.id()==ID_dereference)
  {
    assert(expr.operands().size()==1);
    clean_expr(expr.op0(), dest, mode);
  }
  else if(expr.id()==ID_comma)
  {
    // Yes, one can take the address of a comma expression.
    // Treatment is similar to clean_expr() above.

    exprt result;

    Forall_operands(it, expr)
    {
      bool last=(it==--expr.operands().end());

      // special treatment for last one
      if(last)
        result.swap(*it);
      else
      {
        clean_expr(*it, dest, mode, false);

        // get any side-effects
        if(it->is_not_nil())
          convert(code_expressiont(*it), dest, mode);
      }
    }

    expr.swap(result);

    // do again
    clean_expr_address_of(expr, dest, mode);
  }
  else
    Forall_operands(it, expr)
      clean_expr_address_of(*it, dest, mode);
}

void goto_convertt::remove_gcc_conditional_expression(
  exprt &expr,
  goto_programt &dest,
  const irep_idt &mode)
{
  if(expr.operands().size()!=2)
  {
    error().source_location=expr.find_source_location();
    error() << "conditional_expression takes two operands" << eom;
    throw 0;
  }

  // first remove side-effects from condition
  clean_expr(expr.op0(), dest, mode);

  // now we can copy op0 safely
  if_exprt if_expr;

  if_expr.cond()=expr.op0();
  if_expr.true_case()=expr.op0();
  if_expr.false_case()=expr.op1();
  if_expr.type()=expr.type();
  if_expr.add_source_location()=expr.source_location();

  if(if_expr.cond().type()!=bool_typet())
    if_expr.cond().make_typecast(bool_typet());

  expr.swap(if_expr);

  // there might still be junk in expr.op2()
  clean_expr(expr, dest, mode);
}
