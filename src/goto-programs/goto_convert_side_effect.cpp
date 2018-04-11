/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "goto_convert_class.h"

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/std_expr.h>
#include <util/rename.h>
#include <util/cprover_prefix.h>
#include <util/symbol.h>

#include <util/c_types.h>

bool goto_convertt::has_function_call(const exprt &expr)
{
  forall_operands(it, expr)
    if(has_function_call(*it))
      return true;

  if(expr.id()==ID_side_effect &&
     expr.get(ID_statement)==ID_function_call)
    return true;

  return false;
}

void goto_convertt::remove_assignment(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  const irep_idt statement=expr.get_statement();

  if(statement==ID_assign)
  {
    exprt tmp=expr;
    tmp.id(ID_code);
    // just interpret as code
    convert_assign(to_code_assign(to_code(tmp)), dest);
  }
  else if(statement==ID_assign_plus ||
          statement==ID_assign_minus ||
          statement==ID_assign_mult ||
          statement==ID_assign_div ||
          statement==ID_assign_mod ||
          statement==ID_assign_shl ||
          statement==ID_assign_ashr ||
          statement==ID_assign_lshr ||
          statement==ID_assign_bitand ||
          statement==ID_assign_bitxor ||
          statement==ID_assign_bitor)
  {
    if(expr.operands().size()!=2)
    {
      error().source_location=expr.find_source_location();
      error() << statement << " takes two arguments" << eom;
      throw 0;
    }

    irep_idt new_id;

    if(statement==ID_assign_plus)
      new_id=ID_plus;
    else if(statement==ID_assign_minus)
      new_id=ID_minus;
    else if(statement==ID_assign_mult)
      new_id=ID_mult;
    else if(statement==ID_assign_div)
      new_id=ID_div;
    else if(statement==ID_assign_mod)
      new_id=ID_mod;
    else if(statement==ID_assign_shl)
      new_id=ID_shl;
    else if(statement==ID_assign_ashr)
      new_id=ID_ashr;
    else if(statement==ID_assign_lshr)
      new_id=ID_lshr;
    else if(statement==ID_assign_bitand)
      new_id=ID_bitand;
    else if(statement==ID_assign_bitxor)
      new_id=ID_bitxor;
    else if(statement==ID_assign_bitor)
      new_id=ID_bitor;
    else
    {
      error().source_location=expr.find_source_location();
      error() << "assignment `" << statement << "' not yet supported"
              << eom;
      throw 0;
    }

    exprt rhs;

    const typet &op0_type=ns.follow(expr.op0().type());

    // C/C++ Booleans get very special treatment.
    if(op0_type.id()==ID_c_bool)
    {
      binary_exprt tmp(expr.op0(), new_id, expr.op1(), expr.op1().type());
      tmp.op0().make_typecast(expr.op1().type());
      rhs=typecast_exprt(is_not_zero(tmp, ns), expr.op0().type());
    }
    else
    {
      rhs.id(new_id);
      rhs.copy_to_operands(expr.op0(), expr.op1());
      rhs.type()=expr.op0().type();
      rhs.add_source_location()=expr.source_location();
    }

    code_assignt assignment(expr.op0(), rhs);
    assignment.add_source_location()=expr.source_location();

    convert(assignment, dest);
  }
  else
    UNREACHABLE;

  // revert assignment in the expression to its LHS
  if(result_is_used)
  {
    exprt lhs;
    lhs.swap(expr.op0());
    expr.swap(lhs);
  }
  else
    expr.make_nil();
}

void goto_convertt::remove_pre(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "preincrement/predecrement must have one operand" << eom;
    throw 0;
  }

  const irep_idt statement=expr.get_statement();

  assert(statement==ID_preincrement ||
         statement==ID_predecrement);

  exprt rhs;
  rhs.add_source_location()=expr.source_location();

  if(statement==ID_preincrement)
    rhs.id(ID_plus);
  else
    rhs.id(ID_minus);

  const typet &op_type=ns.follow(expr.op0().type());

  if(op_type.id()==ID_bool)
  {
    rhs.copy_to_operands(expr.op0(), from_integer(1, signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs=is_not_zero(rhs, ns);
  }
  else if(op_type.id()==ID_c_bool)
  {
    rhs.copy_to_operands(expr.op0(), from_integer(1, signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs=is_not_zero(rhs, ns);
    rhs.make_typecast(op_type);
  }
  else if(op_type.id()==ID_c_enum ||
          op_type.id()==ID_c_enum_tag)
  {
    rhs.copy_to_operands(expr.op0(), from_integer(1, signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs.make_typecast(op_type);
  }
  else
  {
    typet constant_type;

    if(op_type.id()==ID_pointer)
      constant_type=index_type();
    else if(is_number(op_type) || op_type.id()==ID_c_bool)
      constant_type=op_type;
    else
    {
      error().source_location=expr.find_source_location();
      error() << "no constant one of type " << op_type.pretty() << eom;
      throw 0;
    }

    exprt constant=from_integer(1, constant_type);

    rhs.copy_to_operands(expr.op0());
    rhs.move_to_operands(constant);
    rhs.type()=expr.op0().type();
  }

  code_assignt assignment(expr.op0(), rhs);
  assignment.add_source_location()=expr.find_source_location();

  convert(assignment, dest);

  if(result_is_used)
  {
    // revert to argument of pre-inc/pre-dec
    exprt tmp=expr.op0();
    expr.swap(tmp);
  }
  else
    expr.make_nil();
}

void goto_convertt::remove_post(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  goto_programt tmp1, tmp2;

  // we have ...(op++)...

  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "postincrement/postdecrement must have one operand"
            << eom;
    throw 0;
  }

  const irep_idt statement=expr.get_statement();

  assert(statement==ID_postincrement ||
         statement==ID_postdecrement);

  exprt rhs;
  rhs.add_source_location()=expr.source_location();

  if(statement==ID_postincrement)
    rhs.id(ID_plus);
  else
    rhs.id(ID_minus);

  const typet &op_type=ns.follow(expr.op0().type());

  if(op_type.id()==ID_bool)
  {
    rhs.copy_to_operands(expr.op0(), from_integer(1, signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs=is_not_zero(rhs, ns);
  }
  else if(op_type.id()==ID_c_bool)
  {
    rhs.copy_to_operands(expr.op0(), from_integer(1, signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs=is_not_zero(rhs, ns);
    rhs.make_typecast(op_type);
  }
  else if(op_type.id()==ID_c_enum ||
          op_type.id()==ID_c_enum_tag)
  {
    rhs.copy_to_operands(expr.op0(), from_integer(1, signed_int_type()));
    rhs.op0().make_typecast(signed_int_type());
    rhs.type()=signed_int_type();
    rhs.make_typecast(op_type);
  }
  else
  {
    typet constant_type;

    if(op_type.id()==ID_pointer)
      constant_type=index_type();
    else if(is_number(op_type) || op_type.id()==ID_c_bool)
      constant_type=op_type;
    else
    {
      error().source_location=expr.find_source_location();
      error() << "no constant one of type " << op_type.pretty() << eom;
      throw 0;
    }

    exprt constant;

    if(constant_type.id()==ID_complex)
    {
      exprt real=from_integer(1, constant_type.subtype());
      exprt imag=from_integer(0, constant_type.subtype());
      constant=complex_exprt(real, imag, to_complex_type(constant_type));
    }
    else
      constant=from_integer(1, constant_type);

    rhs.copy_to_operands(expr.op0());
    rhs.move_to_operands(constant);
    rhs.type()=expr.op0().type();
  }

  code_assignt assignment(expr.op0(), rhs);
  assignment.add_source_location()=expr.find_source_location();

  convert(assignment, tmp2);

  // fix up the expression, if needed

  if(result_is_used)
  {
    exprt tmp=expr.op0();
    make_temp_symbol(tmp, "post", dest);
    expr.swap(tmp);
  }
  else
    expr.make_nil();

  dest.destructive_append(tmp1);
  dest.destructive_append(tmp2);
}

void goto_convertt::remove_function_call(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  if(!result_is_used)
  {
    assert(expr.operands().size()==2);
    code_function_callt call;
    call.function()=expr.op0();
    call.arguments()=expr.op1().operands();
    call.add_source_location()=expr.source_location();
    call.lhs().make_nil();
    convert_function_call(call, dest);
    expr.make_nil();
    return;
  }

  auxiliary_symbolt new_symbol;

  new_symbol.base_name="return_value";
  new_symbol.type=expr.type();
  new_symbol.location=expr.find_source_location();

  // get name of function, if available

  if(expr.id()!=ID_side_effect ||
     expr.get(ID_statement)!=ID_function_call)
  {
    error().source_location=expr.find_source_location();
    error() << "expected function call" << eom;
    throw 0;
  }

  if(expr.operands().empty())
  {
    error().source_location=expr.find_source_location();
    error() << "function_call expects at least one operand" << eom;
    throw 0;
  }

  if(expr.op0().id()==ID_symbol)
  {
    const irep_idt &identifier=expr.op0().get(ID_identifier);
    const symbolt &symbol=lookup(identifier);

    std::string new_base_name=id2string(new_symbol.base_name);

    new_base_name+='_';
    new_base_name+=id2string(symbol.base_name);
    new_base_name += "$0";

    new_symbol.base_name=new_base_name;
    new_symbol.mode=symbol.mode;
  }

  new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);

  // ensure that the name is unique
  new_name(new_symbol);

  {
    code_declt decl;
    decl.symbol()=new_symbol.symbol_expr();
    decl.add_source_location()=new_symbol.location;
    convert_decl(decl, dest);
  }

  {
    goto_programt tmp_program2;
    code_function_callt call;
    call.lhs()=new_symbol.symbol_expr();
    call.function()=expr.op0();
    call.arguments()=expr.op1().operands();
    call.add_source_location()=new_symbol.location;
    convert_function_call(call, dest);
  }

  static_cast<exprt &>(expr)=new_symbol.symbol_expr();
}

void goto_convertt::replace_new_object(
  const exprt &object,
  exprt &dest)
{
  if(dest.id()=="new_object")
    dest=object;
  else
    Forall_operands(it, dest)
      replace_new_object(object, *it);
}

void goto_convertt::remove_cpp_new(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  codet call;

  auxiliary_symbolt new_symbol;

  new_symbol.base_name = "new_ptr$0";
  new_symbol.type=expr.type();
  new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);

  // ensure that the name is unique
  new_name(new_symbol);

  code_declt decl;
  decl.symbol()=new_symbol.symbol_expr();
  decl.add_source_location()=new_symbol.location;
  convert_decl(decl, dest);

  call=code_assignt(new_symbol.symbol_expr(), expr);

  if(result_is_used)
    static_cast<exprt &>(expr)=new_symbol.symbol_expr();
  else
    expr.make_nil();

  convert(call, dest);
}

void goto_convertt::remove_cpp_delete(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  assert(expr.operands().size()==1);

  codet tmp;

  tmp.set_statement(expr.get_statement());
  tmp.add_source_location()=expr.source_location();
  tmp.copy_to_operands(expr.op0());
  tmp.set(ID_destructor, expr.find(ID_destructor));

  convert_cpp_delete(tmp, dest);

  expr.make_nil();
}

void goto_convertt::remove_malloc(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  codet call;

  if(result_is_used)
  {
    auxiliary_symbolt new_symbol;

    new_symbol.base_name = "malloc_value$0";
    new_symbol.type=expr.type();
    new_symbol.name=tmp_symbol_prefix+id2string(new_symbol.base_name);
    new_symbol.location=expr.source_location();

    // ensure that the name is unique
    new_name(new_symbol);

    code_declt decl;
    decl.symbol()=new_symbol.symbol_expr();
    decl.add_source_location()=new_symbol.location;
    convert_decl(decl, dest);

    call=code_assignt(new_symbol.symbol_expr(), expr);
    call.add_source_location()=expr.source_location();

    static_cast<exprt &>(expr)=new_symbol.symbol_expr();
  }
  else
  {
    call=codet(ID_expression);
    call.move_to_operands(expr);
  }

  convert(call, dest);
}

void goto_convertt::remove_temporary_object(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  if(expr.operands().size()!=1 &&
     !expr.operands().empty())
  {
    error().source_location=expr.find_source_location();
    error() << "temporary_object takes 0 or 1 operands" << eom;
    throw 0;
  }

  symbolt &new_symbol = new_tmp_symbol(
    expr.type(), "obj", dest, expr.find_source_location(), expr.get(ID_mode));

  if(expr.operands().size()==1)
  {
    const code_assignt assignment(new_symbol.symbol_expr(), expr.op0());

    convert(assignment, dest);
  }

  if(expr.find(ID_initializer).is_not_nil())
  {
    assert(expr.operands().empty());
    exprt initializer=static_cast<const exprt &>(expr.find(ID_initializer));
    replace_new_object(new_symbol.symbol_expr(), initializer);

    convert(to_code(initializer), dest);
  }

  static_cast<exprt &>(expr)=new_symbol.symbol_expr();
}

void goto_convertt::remove_statement_expression(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  // This is a gcc extension of the form ({ ....; expr; })
  // The value is that of the final expression.
  // The expression is copied into a temporary before the
  // scope is destroyed.

  if(expr.operands().size()!=1)
  {
    error().source_location=expr.find_source_location();
    error() << "statement_expression takes 1 operand" << eom;
    throw 0;
  }

  if(expr.op0().id()!=ID_code)
  {
    error().source_location=expr.op0().find_source_location();
    error() << "statement_expression takes code as operand" << eom;
    throw 0;
  }

  codet &code=to_code(expr.op0());

  if(!result_is_used)
  {
    convert(code, dest);
    expr.make_nil();
    return;
  }

  if(code.get_statement()!=ID_block)
  {
    error().source_location=code.find_source_location();
    error() << "statement_expression takes block as operand" << eom;
    throw 0;
  }

  if(code.operands().empty())
  {
    error().source_location=expr.find_source_location();
    error() << "statement_expression takes non-empty block as operand"
            << eom;
    throw 0;
  }

  // get last statement from block, following labels
  codet &last=to_code_block(code).find_last_statement();

  source_locationt source_location=last.find_source_location();

  symbolt &new_symbol = new_tmp_symbol(
    expr.type(),
    "statement_expression",
    dest,
    source_location,
    expr.get(ID_mode));

  symbol_exprt tmp_symbol_expr(new_symbol.name, new_symbol.type);
  tmp_symbol_expr.add_source_location()=source_location;

  if(last.get(ID_statement)==ID_expression)
  {
    // we turn this into an assignment
    exprt e=to_code_expression(last).expression();
    last=code_assignt(tmp_symbol_expr, e);
    last.add_source_location()=source_location;
  }
  else if(last.get(ID_statement)==ID_assign)
  {
    exprt e=to_code_assign(last).lhs();
    code_assignt assignment(tmp_symbol_expr, e);
    assignment.add_source_location()=source_location;
    code.operands().push_back(assignment);
  }
  else
  {
    error() << "statement_expression expects expression as "
            << "last statement, but got `"
            << last.get(ID_statement) << "'" << eom;
    throw 0;
  }

  {
    goto_programt tmp;
    convert(code, tmp);
    dest.destructive_append(tmp);
  }

  static_cast<exprt &>(expr)=tmp_symbol_expr;
}

void goto_convertt::remove_side_effect(
  side_effect_exprt &expr,
  goto_programt &dest,
  bool result_is_used)
{
  const irep_idt &statement=expr.get_statement();

  if(statement==ID_function_call)
    remove_function_call(expr, dest, result_is_used);
  else if(statement==ID_assign ||
          statement==ID_assign_plus ||
          statement==ID_assign_minus ||
          statement==ID_assign_mult ||
          statement==ID_assign_div ||
          statement==ID_assign_bitor ||
          statement==ID_assign_bitxor ||
          statement==ID_assign_bitand ||
          statement==ID_assign_lshr ||
          statement==ID_assign_ashr ||
          statement==ID_assign_shl ||
          statement==ID_assign_mod)
    remove_assignment(expr, dest, result_is_used);
  else if(statement==ID_postincrement ||
          statement==ID_postdecrement)
    remove_post(expr, dest, result_is_used);
  else if(statement==ID_preincrement ||
          statement==ID_predecrement)
    remove_pre(expr, dest, result_is_used);
  else if(statement==ID_cpp_new ||
          statement==ID_cpp_new_array)
    remove_cpp_new(expr, dest, result_is_used);
  else if(statement==ID_cpp_delete ||
          statement==ID_cpp_delete_array)
    remove_cpp_delete(expr, dest, result_is_used);
  else if(statement==ID_allocate)
    remove_malloc(expr, dest, result_is_used);
  else if(statement==ID_temporary_object)
    remove_temporary_object(expr, dest, result_is_used);
  else if(statement==ID_statement_expression)
    remove_statement_expression(expr, dest, result_is_used);
  else if(statement==ID_nondet)
  {
    // these are fine
  }
  else if(statement==ID_skip)
  {
    expr.make_nil();
  }
  else if(statement==ID_throw)
  {
    goto_programt::targett t=dest.add_instruction(THROW);
    t->code=
      code_expressiont(side_effect_expr_throwt(expr.find(ID_exception_list)));
    t->code.op0().operands().swap(expr.operands());
    t->code.add_source_location()=expr.source_location();
    t->source_location=expr.source_location();

    // the result can't be used, these are void
    expr.make_nil();
  }
  else
  {
    error().source_location=expr.find_source_location();
    error() << "cannot remove side effect (" << statement << ")" << eom;
    throw 0;
  }
}
