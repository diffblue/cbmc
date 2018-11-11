/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_typecheck.h"

#include <util/symbol_table.h>
#include <util/prefix.h>
#include <util/std_expr.h>

#include "expr2jsil.h"
#include "jsil_types.h"

std::string jsil_typecheckt::to_string(const exprt &expr)
{
  return expr2jsil(expr, ns);
}

std::string jsil_typecheckt::to_string(const typet &type)
{
  return type2jsil(type, ns);
}

/// Prefix parameters and variables with a procedure name
irep_idt jsil_typecheckt::add_prefix(const irep_idt &ds)
{
  return id2string(proc_name) + "::" + id2string(ds);
}

void jsil_typecheckt::update_expr_type(exprt &expr, const typet &type)
{
  expr.type()=type;

  if(expr.id()==ID_symbol)
  {
    const irep_idt &id=to_symbol_expr(expr).get_identifier();

    const auto maybe_symbol=symbol_table.get_writeable(id);
    if(!maybe_symbol)
    {
      error() << "unexpected symbol: " << id << eom;
      throw 0;
    }

    symbolt &s=*maybe_symbol;
    if(s.type.id().empty() || s.type.is_nil())
      s.type=type;
    else
      s.type=jsil_union(s.type, type);
  }
}

void jsil_typecheckt::make_type_compatible(
    exprt &expr,
    const typet &type,
    bool must)
{
  if(type.id().empty() || type.is_nil())
  {
    error().source_location = expr.source_location();
    error() << "make_type_compatible got empty type: " << expr.pretty() << eom;
    throw 0;
  }

  if(expr.type().id().empty() || expr.type().is_nil())
  {
    // Type is not yet set
    update_expr_type(expr, type);
    return;
  }

  if(must)
  {
    if(jsil_incompatible_types(expr.type(), type))
    {
      error().source_location = expr.source_location();
      error() << "failed to typecheck expr "
              << expr.pretty() << " with type "
              << expr.type().pretty()
              << "; required type " << type.pretty() << eom;
      throw 0;
    }
  }
  else if(!jsil_is_subtype(type, expr.type()))
  {
    // Types are not compatible
    typet upper=jsil_union(expr.type(), type);
    update_expr_type(expr, upper);
  }
}

void jsil_typecheckt::typecheck_type(typet &type)
{
  if(type.id()==ID_code)
  {
    code_typet &parameters=to_code_type(type);

    for(code_typet::parametert &p : parameters.parameters())
    {
      // create new symbol
      parameter_symbolt new_symbol;
      new_symbol.base_name=p.get_identifier();

      // append procedure name to parameters
      p.set_identifier(add_prefix(p.get_identifier()));
      new_symbol.name=p.get_identifier();

      if(is_jsil_builtin_code_type(type))
        new_symbol.type=jsil_value_or_empty_type();
      else if(is_jsil_spec_code_type(type))
        new_symbol.type=jsil_value_or_reference_type();
      else
        new_symbol.type=jsil_value_type(); // User defined function

      new_symbol.mode="jsil";

      // mark as already typechecked
      new_symbol.is_extern=true;

      if(symbol_table.add(new_symbol))
      {
        error() << "failed to add parameter symbol `"
                << new_symbol.name << "' in the symbol table" << eom;
        throw 0;
      }
    }
  }
}

void jsil_typecheckt::typecheck_expr(exprt &expr)
{
  // first do sub-nodes
  typecheck_expr_operands(expr);

  // now do case-split
  typecheck_expr_main(expr);
}

void jsil_typecheckt::typecheck_expr_operands(exprt &expr)
{
  Forall_operands(it, expr)
    typecheck_expr(*it);
}

void jsil_typecheckt::typecheck_expr_main(exprt &expr)
{
  if(expr.id()==ID_code)
  {
    error().source_location = expr.source_location();
    error() << "typecheck_expr_main got code: " << expr.pretty() << eom;
    throw 0;
  }
  else if(expr.id()==ID_symbol)
    typecheck_symbol_expr(to_symbol_expr(expr));
  else if(expr.id()==ID_constant)
  {
  }
  else
  {
    // expressions are expected not to have type set just yet
    assert(expr.type().is_nil() || expr.type().id().empty());

    if(expr.id()==ID_null ||
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
            expr.id()==ID_pointer ||
            expr.id()==ID_member ||
            expr.id()=="variable")
      expr.type()=jsil_kind();
    else if(expr.id()=="proto" ||
            expr.id()=="fid" ||
            expr.id()=="scope" ||
            expr.id()=="constructid" ||
            expr.id()=="primvalue" ||
            expr.id()=="targetfunction" ||
            expr.id()==ID_class)
    {
      // TODO: have a special type for builtin fields
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
      expr.type()=floatbv_typet();
    }
    else if(expr.id()=="num_to_string")
    {
      typecheck_expr_unary_num(expr);
      expr.type()=string_typet();
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
            expr.id()==ID_mod ||
            expr.id()==ID_bitand ||
            expr.id()==ID_bitor ||
            expr.id()==ID_bitxor ||
            expr.id()==ID_shl ||
            expr.id()==ID_shr ||
            expr.id()==ID_lshr)
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
      expr.type()=jsil_kind();
    else if(expr.id()=="new")
      expr.type()=jsil_user_object_type();
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
    else if(expr.id()==ID_side_effect)
      typecheck_expr_side_effect_throw(to_side_effect_expr_throw(expr));
    else
    {
      error().source_location = expr.source_location();
      error() << "unexpected expression: " << expr.pretty() << eom;
      throw 0;
    }
  }
}

void jsil_typecheckt::typecheck_expr_side_effect_throw(
  side_effect_expr_throwt &expr)
{
  irept &excep_list=expr.add(ID_exception_list);
  assert(excep_list.id()==ID_symbol);
  symbol_exprt &s=static_cast<symbol_exprt &>(excep_list);
  typecheck_symbol_expr(s);
}

void jsil_typecheckt::typecheck_expr_constant(exprt &expr)
{
  if(expr.id()==ID_null)
    expr.type()=jsil_null_type();
  else if(expr.id()=="undefined")
    expr.type()=jsil_undefined_type();
  else if(expr.id()==ID_empty)
    expr.type()=jsil_empty_type();
}

void jsil_typecheckt::typecheck_expr_proto_field(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_object_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  expr.type()=jsil_value_or_empty_type();
}

void jsil_typecheckt::typecheck_expr_proto_obj(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands";
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_object_type(), true);
  make_type_compatible(expr.op1(), jsil_object_type(), true);

  expr.type()=bool_typet();
}

void jsil_typecheckt::typecheck_expr_delete(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_object_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  expr.type()=bool_typet();
}

void jsil_typecheckt::typecheck_expr_index(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_object_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  // special case for function identifiers
  if(expr.op1().id()=="fid" || expr.op1().id()=="constructid")
    expr.type()=code_typet();
  else
    expr.type()=jsil_value_type();
}

void jsil_typecheckt::typecheck_expr_has_field(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_object_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  expr.type()=bool_typet();
}

void jsil_typecheckt::typecheck_expr_field(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects single operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_reference_type(), true);

  expr.type()=string_typet();
}

void jsil_typecheckt::typecheck_expr_base(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects single operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_reference_type(), true);

  expr.type()=jsil_value_type();
}

void jsil_typecheckt::typecheck_expr_ref(exprt &expr)
{
  if(expr.operands().size()!=3)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects three operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_value_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  exprt &operand3=expr.op2();
  make_type_compatible(operand3, jsil_kind(), true);

  if(operand3.id()==ID_member)
    expr.type()=jsil_member_reference_type();
  else if(operand3.id()=="variable")
    expr.type()=jsil_variable_reference_type();
  else
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects reference type in the third parameter. Got:"
            << operand3.pretty() << eom;
    throw 0;
  }
}

void jsil_typecheckt::typecheck_expr_concatenation(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), string_typet(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  expr.type()=string_typet();
}

void jsil_typecheckt::typecheck_expr_subtype(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), jsil_kind(), true);
  make_type_compatible(expr.op1(), jsil_kind(), true);

  expr.type()=bool_typet();
}

void jsil_typecheckt::typecheck_expr_binary_boolean(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), bool_typet(), true);
  make_type_compatible(expr.op1(), bool_typet(), true);

  expr.type()=bool_typet();
}

void jsil_typecheckt::typecheck_expr_binary_arith(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }


  make_type_compatible(expr.op0(), floatbv_typet(), true);
  make_type_compatible(expr.op1(), floatbv_typet(), true);

  expr.type()=floatbv_typet();
}

void jsil_typecheckt::typecheck_exp_binary_equal(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  // operands can be of any types

  expr.type()=bool_typet();
}

void jsil_typecheckt::typecheck_expr_binary_compare(exprt &expr)
{
  if(expr.operands().size()!=2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), floatbv_typet(), true);
  make_type_compatible(expr.op1(), floatbv_typet(), true);

  expr.type()=bool_typet();
}

void jsil_typecheckt::typecheck_expr_unary_boolean(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects one operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), bool_typet(), true);

  expr.type()=bool_typet();
}

void jsil_typecheckt::typecheck_expr_unary_string(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects one operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), string_typet(), true);

  expr.type()=floatbv_typet();
}

void jsil_typecheckt::typecheck_expr_unary_num(exprt &expr)
{
  if(expr.operands().size()!=1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects one operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), floatbv_typet(), true);
}

void jsil_typecheckt::typecheck_symbol_expr(symbol_exprt &symbol_expr)
{
  irep_idt identifier=symbol_expr.get_identifier();

  // if this is a built-in identifier, check if it exists in the
  // symbol table and retrieve it's type
  // TODO: add a flag for not needing to prefix internal symbols
  // that do not start with hash
  if(has_prefix(id2string(identifier), "#") ||
     identifier=="eval" ||
     identifier=="nan")
  {
    symbol_tablet::symbolst::const_iterator s_it=
      symbol_table.symbols.find(identifier);

    if(s_it==symbol_table.symbols.end())
    {
      error() << "unexpected internal symbol: " << identifier << eom;
      throw 0;
    }
    else
    {
      // symbol already exists
      const symbolt &symbol=s_it->second;

      // type the expression
      symbol_expr.type()=symbol.type;
    }
  }
  else
  {
    // if this is a variable, we need to check if we already
    // prefixed it and add to the symbol table if it is not there already
    irep_idt identifier_base = identifier;
    if(!has_prefix(id2string(identifier), id2string(proc_name)))
    {
      identifier = add_prefix(identifier);
      symbol_expr.set_identifier(identifier);
    }

    symbol_tablet::symbolst::const_iterator s_it=
    symbol_table.symbols.find(identifier);

    if(s_it==symbol_table.symbols.end())
    {
      // create new symbol
      symbolt new_symbol;
      new_symbol.name=identifier;
      new_symbol.type=symbol_expr.type();
      new_symbol.base_name=identifier_base;
      new_symbol.mode="jsil";
      new_symbol.is_type=false;
      new_symbol.is_lvalue=new_symbol.type.id()!=ID_code;

      // mark as already typechecked
      new_symbol.is_extern=true;

      if(symbol_table.add(new_symbol))
      {
        error() << "failed to add symbol `"
                << new_symbol.name << "' in the symbol table"
                << eom;
        throw 0;
      }
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

void jsil_typecheckt::typecheck_code(codet &code)
{
  const irep_idt &statement=code.get_statement();

  if(statement==ID_function_call)
    typecheck_function_call(to_code_function_call(code));
  else if(statement==ID_return)
    typecheck_return(to_code_return(code));
  else if(statement==ID_expression)
  {
    if(code.operands().size()!=1)
    {
      error().source_location = code.source_location();
      error() << "expression statement expected to have one operand"
              << eom;
      throw 0;
    }

    typecheck_expr(code.op0());
  }
  else if(statement==ID_label)
  {
    typecheck_code(to_code_label(code).code());
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
    typecheck_assign(to_code_assign(code));
  else if(statement==ID_try_catch)
    typecheck_try_catch(to_code_try_catch(code));
  else if(statement==ID_skip)
  {
  }
  else
  {
    error().source_location = code.source_location();
    error() << "unexpected statement: " << statement << eom;
    throw 0;
  }
}

void jsil_typecheckt::typecheck_return(code_returnt &code)
{
  if(code.has_return_value())
    typecheck_expr(code.return_value());
}

void jsil_typecheckt::typecheck_block(codet &code)
{
  Forall_operands(it, code)
    typecheck_code(to_code(*it));
}

void jsil_typecheckt::typecheck_try_catch(code_try_catcht &code)
{
  // A special case of try catch with one catch clause
  if(code.operands().size()!=3)
  {
    error().source_location = code.source_location();
    error() << "try_catch expected to have three operands" << eom;
    throw 0;
  }

  // function call
  typecheck_function_call(to_code_function_call(code.try_code()));

  // catch decl is not used, but is required by goto-programs

  typecheck_code(code.get_catch_code(0));
}

void jsil_typecheckt::typecheck_function_call(
  code_function_callt &call)
{
  if(call.operands().size()!=3)
  {
    error().source_location = call.source_location();
    error() << "function call expected to have three operands" << eom;
    throw 0;
  }

  exprt &lhs=call.lhs();
  typecheck_expr(lhs);

  exprt &f=call.function();
  typecheck_expr(f);

  for(auto &arg : call.arguments())
    typecheck_expr(arg);

  // Look for a function declaration symbol in the symbol table
  if(f.id()==ID_symbol)
  {
    const irep_idt &id=to_symbol_expr(f).get_identifier();

    if(const auto maybe_symbol=symbol_table.lookup(id))
    {
      const symbolt &s=*maybe_symbol;

      if(s.type.id()==ID_code)
      {
        const code_typet &codet=to_code_type(s.type);

        for(std::size_t i=0; i<codet.parameters().size(); i++)
        {
          if(i>=call.arguments().size())
            break;

          const typet &param_type=codet.parameters()[i].type();

          if(!param_type.id().empty() && param_type.is_not_nil())
          {
             // check argument's type if parameter's type is given
             make_type_compatible(call.arguments()[i], param_type, true);
          }
        }

        // if there are too few arguments, add undefined
        if(codet.parameters().size()>call.arguments().size())
        {
          for(std::size_t i=call.arguments().size();
              i<codet.parameters().size();
              ++i)
            call.arguments().push_back(
              exprt("undefined", jsil_undefined_type()));
        }

        // if there are too many arguments, remove
        while(codet.parameters().size()<call.arguments().size())
          call.arguments().pop_back();

        // check return type if exists
        if(!codet.return_type().id().empty() &&
            codet.return_type().is_not_nil())
          make_type_compatible(lhs, codet.return_type(), true);
        else make_type_compatible(lhs, jsil_any_type(), true);
      }
      else
      {
        // TODO: a symbol can be a variable evaluating to a string
        // which corresponds to a function identifier
        make_type_compatible(lhs, jsil_any_type(), true);
      }
    }
    else
    {
      // Should be function, declaration not found yet
      symbolt new_symbol;
      new_symbol.name=id;
      new_symbol.type=code_typet();
      new_symbol.mode="jsil";
      new_symbol.is_type=false;
      new_symbol.value=exprt("no-body-just-yet");

      make_type_compatible(lhs, jsil_any_type(), true);

      if(symbol_table.add(new_symbol))
      {
        error().source_location=new_symbol.location;
        error() << "failed to add expression symbol to symbol table"
                << eom;
        throw 0;
      }
    }
  }
  else
  {
    // TODO: this might be a string literal
    // which corresponds to a function identifier
    make_type_compatible(lhs, jsil_any_type(), true);
  }
}

void jsil_typecheckt::typecheck_ifthenelse(code_ifthenelset &code)
{
  exprt &cond=code.cond();
  typecheck_expr(cond);
  make_type_compatible(cond, bool_typet(), true);

  typecheck_code(code.then_case());

  if(!code.else_case().is_nil())
    typecheck_code(code.else_case());
}

void jsil_typecheckt::typecheck_assign(code_assignt &code)
{
  typecheck_expr(code.op0());
  typecheck_expr(code.op1());

  make_type_compatible(code.op0(), code.op1().type(), false);
}

/// typechecking procedure declaration; any other symbols should have been
/// typechecked during typechecking of procedure declaration
/// \par parameters: any symbol
void jsil_typecheckt::typecheck_non_type_symbol(symbolt &symbol)
{
  assert(!symbol.is_type);

  // Using is_extern to check if symbol was already typechecked
  if(symbol.is_extern)
    return;
  if(symbol.value.id()!="no-body-just-yet")
    symbol.is_extern=true;

  proc_name=symbol.name;
  typecheck_type(symbol.type);

  if(symbol.value.id()==ID_code)
    typecheck_code(to_code(symbol.value));
  else if(symbol.name=="eval")
  {
    // No code for eval. Do nothing
  }
  else if(symbol.value.id()=="no-body-just-yet")
  {
    // Do nothing
  }
  else
  {
    error().source_location=symbol.location;
    error() << "non-type symbol value expected code, but got "
            << symbol.value.pretty() << eom;
    throw 0;
  }
}

void jsil_typecheckt::typecheck()
{
  // The hash table iterators are not stable,
  // and we might add new symbols.

  std::vector<irep_idt> identifiers;
  identifiers.reserve(symbol_table.symbols.size());
  for(const auto &symbol_pair : symbol_table.symbols)
  {
    identifiers.push_back(symbol_pair.first);
  }

  // We first check all type symbols,
  // recursively doing base classes first.
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=*symbol_table.get_writeable(id);
    if(symbol.is_type)
      typecheck_type_symbol(symbol);
  }

  // We now check all non-type symbols
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol=*symbol_table.get_writeable(id);
    if(!symbol.is_type)
      typecheck_non_type_symbol(symbol);
  }
}

bool jsil_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  jsil_typecheckt jsil_typecheck(symbol_table, message_handler);
  return jsil_typecheck.typecheck_main();
}

bool jsil_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &)
{
  const unsigned errors_before=
    message_handler.get_message_count(messaget::M_ERROR);

  symbol_tablet symbol_table;

  jsil_typecheckt jsil_typecheck(
    symbol_table,
    message_handler);

  try
  {
    jsil_typecheck.typecheck_expr(expr);
  }

  catch(int)
  {
    jsil_typecheck.error();
  }

  catch(const char *e)
  {
    jsil_typecheck.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    jsil_typecheck.error() << e << messaget::eom;
  }

  return message_handler.get_message_count(messaget::M_ERROR)!=errors_before;
}
