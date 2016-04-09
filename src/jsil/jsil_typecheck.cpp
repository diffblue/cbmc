/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

#include <util/symbol_table.h>
#include <util/prefix.h>

#include "expr2jsil.h"
#include "jsil_types.h"

#include "jsil_typecheck.h"

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string jsil_typecheckt::to_string(const exprt &expr)
{
  return expr2jsil(expr, ns);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string jsil_typecheckt::to_string(const typet &type)
{
  return type2jsil(type, ns);
}

/*******************************************************************\

Function: jsil_typecheckt::add_prefix

  Inputs:

 Outputs:

 Purpose: Prefix parameters and variables with a procedure name

\*******************************************************************/

irep_idt jsil_typecheckt::add_prefix(const irep_idt &ds)
{
	return id2string(proc_name)+"::"+id2string(ds);
}

/*******************************************************************\

Function: jsil_typecheckt::update_expr_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void jsil_typecheckt::update_expr_type(exprt &expr, const typet &type)
{
  expr.type()=type;

  if(expr.id()==ID_symbol)
  {
    symbol_exprt &sexpr=to_symbol_expr(expr);
    const irep_idt &id=sexpr.get_identifier();

    if(!symbol_table.has_symbol(id))
      throw "Unexpected symbol "+id2string(id);

    symbolt &s=symbol_table.lookup(id);
    if(s.type.id_string().empty() || s.type.is_nil())
      s.type=type;
    else
      s.type=jsil_union(s.type, type);
  }
}

/*******************************************************************\

Function: jsil_typecheckt::make_type_compatible

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::make_type_compatible(
  exprt &expr,
  const typet &type,
  bool must)
{
  if(expr.type().id().empty() || expr.type().is_nil())
  {
    // Type is not yet set
    update_expr_type(expr, type);
    return;
  }

  if(must)
  {
    if(jsil_union_typet(expr.type()).intersect_with(
        jsil_union_typet(type)).components().empty())
      throw "Failed to typecheck expr "+expr.pretty()+
        " with type "+expr.type().pretty()+"; required type "+
        type.pretty();
  }
  else
  {
    if(!jsil_is_subtype(type, expr.type()))
    {
      // Types are not compatible
      typet upper=jsil_union(expr.type(), type);
      update_expr_type(expr, upper);
    }
  }
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_type(typet &type)
{
  if(type.id()==ID_code)
  {
    code_typet &parameters=to_code_type(type);

    for (code_typet::parametert& p : parameters.parameters())
    {
      // create the symbol
      parameter_symbolt new_symbol;
      new_symbol.base_name=p.get_identifier();
      // appending procedure name to parameters
      p.set_identifier(add_prefix(p.get_identifier()));
      new_symbol.name=p.get_identifier();

      if(is_jsil_builtin_code_type(type))
        new_symbol.type=jsil_value_or_emptyt();
      else if(is_jsil_spec_code_type(type))
        new_symbol.type=jsil_value_or_referencet();
      else
        // User defined function
        new_symbol.type=jsil_valuet();

      new_symbol.mode="jsil";

      if(symbol_table.add(new_symbol))
        throw "failed to add parameter symbol";
    }
  }
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr(exprt &expr)
{
  // first do sub-nodes
  typecheck_expr_operands(expr);

  // now do case-split
  typecheck_expr_main(expr);
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_expr_operands

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_operands(exprt &expr)
{
  Forall_operands(it, expr)
    typecheck_expr(*it);
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_expr_main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_main(exprt &expr)
{
  if(expr.id()==ID_code)
  {
    err_location(expr);
    str << "typecheck_expr_main got code: " << expr.pretty();
    throw 0;
  }
  else if(expr.id()==ID_symbol)
    typecheck_symbol_expr(to_symbol_expr (expr));
  else if(expr.id()==ID_side_effect)
    typecheck_expr_side_effect(to_side_effect_expr(expr));
  else if(expr.id()==ID_constant ||
          expr.id()==ID_string_constant ||
          expr.id()==ID_null ||
          expr.id()=="undefined" ||
          expr.id()==ID_empty)
    typecheck_expr_constant(expr);
  else if(expr.id()=="null_type" ||
          expr.id()=="undefined_type" ||
          expr.id()==ID_boolean ||
          expr.id()==ID_string ||
          expr.id()=="number" ||
          expr.id()=="builtin_object" ||
          expr.id()=="user_object" ||
          expr.id()=="object" ||
          expr.id()==ID_reference ||
          expr.id()==ID_member ||
          expr.id()=="variable")
    expr.type()=jsil_kindt();
  else if(expr.id()=="proto" ||
          expr.id()=="fid" ||
          expr.id()=="scope" ||
          expr.id()=="constructid" ||
          expr.id()=="primvalue" ||
          expr.id()=="targetfunction" ||
          expr.id()==ID_class)
  {
    // TODO: builtin fields -- do we want special field type?
    expr.type()=string_typet();
  }
  else if(expr.id()==ID_not)
    typecheck_expr_unary_boolean(expr);
  else if(expr.id()=="string_to_num")
    typecheck_expr_unary_string(expr);
  else if(expr.id()==ID_unary_minus ||
          expr.id()=="num_to_int32" ||
          expr.id()=="num_to_uint32" ||
          expr.id()==ID_bitnot)
  {
    typecheck_expr_unary_num(expr);
    expr.type() = floatbv_typet();
  }
  else if(expr.id()=="num_to_string")
  {
    typecheck_expr_unary_num(expr);
    expr.type() = string_typet();
  }
  else if(expr.id()==ID_equal)
    typecheck_exp_binary_equal(expr);
  else if(expr.id()==ID_lt ||
          expr.id()==ID_le)
    typecheck_expr_binary_compare(expr);
  else if(expr.id()==ID_plus ||
          expr.id()==ID_minus ||
          expr.id()==ID_mult ||
          expr.id()==ID_div ||
          expr.id()==ID_mod)
    typecheck_expr_binary_arith(expr);
  else if(expr.id()==ID_and ||
          expr.id()==ID_or)
    typecheck_expr_binary_boolean(expr);
  else if(expr.id()=="subtype_of")
    typecheck_expr_subtype(expr);
  else if(expr.id()==ID_concatenation)
    typecheck_expr_concatenation(expr);
  else if(expr.id()=="ref")
    typecheck_expr_ref(expr);
  else if(expr.id()=="field")
    typecheck_expr_field(expr);
  else if(expr.id()==ID_base)
    typecheck_expr_base(expr);
  else if(expr.id()==ID_typeof)
    expr.type()=jsil_kindt();
  else if(expr.id()=="new")
    expr.type()=jsil_user_objectt();
  else if(expr.id()=="hasField")
    typecheck_expr_has_field(expr);
  else if(expr.id()==ID_index)
    typecheck_expr_index(expr);
  else if(expr.id()=="delete")
    typecheck_expr_delete(expr);
  else if(expr.id()=="protoField")
    typecheck_expr_proto_field(expr);
  else if(expr.id()=="protoObj")
    typecheck_expr_proto_obj(expr);
  else if(expr.is_nil())
  {
    assert(false);
  }
  else
  {
    err_location(expr);
    str << "unexpected expression: " << expr.pretty();
    throw 0;
  }
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_constant(exprt &expr)
{
  // no need to typecheck ID_constant
  // TODO: make compatible with string_typet
  //  (expr.id()==ID_string_constant)
  if(expr.id()==ID_null)
    expr.type()=jsil_nullt();
  else if(expr.id()=="undefined")
    expr.type()=jsil_undefinedt();
  else if(expr.id()==ID_empty)
    expr.type()=empty_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_proto_field

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_proto_field(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_objectt(), true);

  exprt &operand2=expr.op1();
  make_type_compatible(operand2, string_typet(), true);

  expr.type()=jsil_value_or_emptyt();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_proto_field

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_proto_obj(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_objectt(), true);

  exprt &operand2=expr.op1();
  make_type_compatible(operand2, jsil_objectt(), true);

  expr.type()=bool_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_delete

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_delete(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_objectt(), true);

  exprt &operand2=expr.op1();
  make_type_compatible(operand2, string_typet(), true);

  expr.type()=bool_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_hasfield

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_index(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_objectt(), true);

  exprt &operand2=expr.op1();
  make_type_compatible(operand2, string_typet(), true);

  expr.type()=jsil_valuet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_hasfield

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_has_field(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_objectt(), true);

  exprt &operand2=expr.op1();
  make_type_compatible(operand2, string_typet(), true);

  expr.type()=bool_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_field

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_field(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects single operand";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_referencet(), true);

  expr.type()=string_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_base

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_base(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects single operand";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_referencet(), true);

  // TODO: can we be more precise here we know something more about op0?
  expr.type()=jsil_valuet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_ref

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_ref(exprt &expr)
{
  if(expr.operands().size()!=3)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects three operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_valuet(), true);
  exprt &operand2=expr.op1();
  // TODO: do we want a new field type? since we have built-in fields
  make_type_compatible(operand2, string_typet(), true);
  exprt &operand3=expr.op2();
  make_type_compatible(operand3, jsil_kindt(), true);

  if(operand3.id()==ID_member)
    expr.type()=jsil_member_referencet();
  else if(operand3.id()=="variable")
    expr.type()=jsil_variable_referencet();
  else
  {
    err_location(expr);
    str << "operator `" << expr.id()
      << "' expects reference type in the third parameter. But got:"
      << operand3.pretty();
    throw 0;
  }
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_concatenation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_concatenation(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, string_typet(), true);
  exprt &operand2=expr.op1();
  make_type_compatible(operand2, string_typet(), true);

  expr.type()=string_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_subtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_subtype(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, jsil_kindt(), true);
  exprt &operand2=expr.op1();
  make_type_compatible(operand2, jsil_kindt(), true);

  expr.type()=bool_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_binary_boolean

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_binary_boolean(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, bool_typet(), true);
  exprt &operand2=expr.op1();
  make_type_compatible(operand2, bool_typet(), true);

  expr.type()=bool_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_binary_arith

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_binary_arith(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, floatbv_typet(), true);
  exprt &operand2=expr.op1();
  make_type_compatible(operand2, floatbv_typet(), true);

  expr.type()=floatbv_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_exp_binary_equal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_exp_binary_equal(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

 // operands can be of any types

  expr.type()=bool_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_binary_compare

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_binary_compare(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  exprt &operand1=expr.op0();
  make_type_compatible(operand1, floatbv_typet(), true);
  exprt &operand2=expr.op1();
  make_type_compatible(operand2, floatbv_typet(), true);

  expr.type()=bool_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_unary_boolean

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_unary_boolean(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects one operand";
    throw 0;
  }

  exprt &operand=expr.op0();
  make_type_compatible(operand, bool_typet(), true);

  expr.type()=bool_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_unary_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_unary_string(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "operator `" << expr.id()
        << "' expects one operand";
    throw 0;
  }

  exprt &operand=expr.op0();
  make_type_compatible(operand, string_typet(), true);

  expr.type()=floatbv_typet();
}

/*******************************************************************\

Function: jsil_typecheck_baset::typecheck_expr_unary_num

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_expr_unary_num(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    err_location(expr);
    str << "operator `" << expr.id() << "' expects one operand";
    throw 0;
  }

  exprt &operand=expr.op0();
  make_type_compatible(operand, floatbv_typet(), true);
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_symbol_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_symbol_expr(symbol_exprt &symbol_expr)
{
  irep_idt identifier=symbol_expr.get_identifier();

  // if it is another identifier, such as #lop, #builtin-fid
  // check if it is in the table and add it's type
  if(has_prefix(id2string(identifier), "#"))
  {
    // does it exist already in the symbol table?
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(identifier);

    if(s_it==symbol_table.symbols.end())
      throw "Unexpected internal symbol: "+id2string(identifier);
  }
  else
  {
    // if it is a variable, we need to check if we already prefixed it
    // and add to the table if it is not there already
    irep_idt identifier_base = identifier;
    if(!has_prefix(id2string(identifier), id2string(proc_name)))
    {
      identifier = add_prefix(identifier);
      symbol_expr.set_identifier(identifier);
    }

    // does it exist already in the symbol table?
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(identifier);

    if(s_it==symbol_table.symbols.end())
    {
      // no, create the symbol
      symbolt new_symbol;
      new_symbol.name=identifier;
      new_symbol.type=symbol_expr.type();
      new_symbol.base_name=identifier_base;
      new_symbol.mode="jsil";
      new_symbol.is_type=false;

      if(new_symbol.type.id()==ID_code)
        new_symbol.is_lvalue=false;
      else
        new_symbol.is_lvalue=true;

      if(symbol_table.add(new_symbol))
        throw "failed to add expression symbol to symbol table";
    }
    else
    {
      // symbol already exists
      assert(!s_it->second.is_type);

      const symbolt &symbol=s_it->second;

      // type the expression
      symbol_expr.type()=symbol.type;
    }
  }
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_code(codet &code)
{
  const irep_idt &statement=code.get_statement();

  if(statement==ID_function_call)
    typecheck_function_call(to_code_function_call(code));
  if(statement==ID_decl)
    typecheck_decl(to_code_decl(code));
  else if(statement==ID_return)
    typecheck_return(code);
  else if(statement==ID_expression)
  {
    if(code.operands().size()!=1)
      throw "expression statement expected to have one operand";
    exprt &op=code.op0();
    typecheck_expr(op);
  }
  else if(statement==ID_label)
  {
    // TODO: produce defined label set
  }
  else if(statement==ID_block)
    typecheck_block(code);
  else if(statement==ID_ifthenelse)
    typecheck_ifthenelse(to_code_ifthenelse(code));
  else if(statement==ID_goto)
  {
    // TODO: produce used label set
  }
  else if(statement==ID_assign)
    typecheck_assign(code);
  else if(statement==ID_try_catch)
    typecheck_try_catch(to_code_try_catch(code));
  else if(statement==ID_skip)
  {
  }
  else
  {
    err_location(code);
    str << "unexpected statement: " << statement;
    throw 0;
  }
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_block(codet &code)
{
  Forall_operands(it, code)
    typecheck_code(to_code(*it));
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_try_catch

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_try_catch(code_try_catcht &code)
{
  // A special case of try catch with one catch clause
  if(code.operands().size()!=3)
    throw "try_catch expected to have three operands";

  codet &try_code=code.try_code();
  // function call
  typecheck_function_call(to_code_function_call(try_code));

  code_declt &decl_code=code.get_catch_decl(0);
  typecheck_decl(decl_code);

  codet &catch_code=code.get_catch_code(0);
  typecheck_code(catch_code);
}


/*******************************************************************\

Function: jsil_typecheckt::typecheck_ifthenelse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_ifthenelse(code_ifthenelset &code)
{
  if(code.operands().size()!=3)
    throw "ifthenelse expected to have three operands";

  exprt &cond=code.cond();

  typecheck_expr(cond);
  make_type_compatible(cond, bool_typet(), true);

  typecheck_code(to_code(code.then_case()));

  if(!code.else_case().is_nil())
    typecheck_code(to_code(code.else_case()));
}

/*******************************************************************\

Function: jsil_typecheckt::typecheck_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_assign(codet &code)
{
  if(code.operands().size()!=2)
    throw "assignment statement expected to have two operands";

  typecheck_expr(code.op0());
  typecheck_expr(code.op1());

  make_type_compatible(code.op0(), code.op1().type(), false);
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck_non_type_symbol

  Inputs: symbol denotes a procedure declaration

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck_non_type_symbol(symbolt &symbol)
{
  assert(!symbol.is_type);
  proc_name = symbol.name;
  typecheck_type(symbol.type);
  if (symbol.value.is_nil()) {}
  else if (symbol.value.id()==ID_code)
  typecheck_code(to_code(symbol.value));
  else throw ("Non type symbol value " + symbol.value.pretty());

  // TODO: mark as 'already typechecked'
}

/*******************************************************************\

Function: java_bytecode_typecheckt::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsil_typecheckt::typecheck()
{
  // The hash table iterators are not stable,
  // and we might add new symbols.

  std::vector<irep_idt> identifiers;
  identifiers.reserve(symbol_table.symbols.size());
  forall_symbols(s_it, symbol_table.symbols)
    identifiers.push_back(s_it->first);

  // We first check all type symbols,
  // recursively doing base classes first.
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=symbol_table.symbols[id];

    if(symbol.is_type)
      typecheck_type_symbol(symbol);
  }

  // We now check all non-type symbols
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=symbol_table.symbols[id];

    if(!symbol.is_type)
      typecheck_non_type_symbol(symbol);
  }
}

/*******************************************************************\

Function: jsil_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  jsil_typecheckt jsil_typecheck(symbol_table, message_handler);
  return jsil_typecheck.typecheck_main();
}

/*******************************************************************\

Function: jsil_typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool jsil_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  symbol_tablet symbol_table;

  jsil_typecheckt jsil_typecheck(
    symbol_table,
    message_handler);

  try
  {
    jsil_typecheck.typecheck_expr(expr);
  }

  catch(int e)
  {
    jsil_typecheck.error_msg();
  }

  catch(const char *e)
  {
    jsil_typecheck.str << e;
    jsil_typecheck.error_msg();
  }

  catch(const std::string &e)
  {
    jsil_typecheck.str << e;
    jsil_typecheck.error_msg();
  }

  return jsil_typecheck.get_error_found();
}
