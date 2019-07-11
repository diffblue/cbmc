/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory
// Some sections are left unchanged -- many of which still need to be changed

/// \file
/// Rust Language
#include "rust_typecheck.h"

#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

// #include "expr2rust.h"
#include "rust_types.h"

std::string rust_typecheckt::to_string(const exprt &expr)
{
  return ""; // expr2rust(expr, ns);
}

std::string rust_typecheckt::to_string(const typet &type)
{
  return ""; // type2rust(type, ns);
}

typet rust_typecheckt::lookup_type(exprt &expr)
{
  // unwrap code_expressiont
  if(expr.id() == ID_code && to_code(expr).get_statement() == ID_expression)
    expr = expr.op0();

  if(expr.id() == ID_symbol)
    return search_known_symbols(to_symbol_expr(expr).get_identifier());
  else if(expr.id() == ID_side_effect)
  {
    side_effect_exprt &seexpr = to_side_effect_expr(expr);
    if(seexpr.get_statement() == ID_function_call)
    {
      const auto &func =
        symbol_table.lookup(to_symbol_expr(seexpr.op0()).get_identifier());
      if(func == nullptr)
      {
        error() << "Unable to find function in symbol table: \n"
                << to_symbol_expr(seexpr.op0()).pretty() << eom;
        throw 0;
      }
      return to_code_type(func->type).return_type();
    }
  }
  else
  {
    error() << "Unable to lookup type for expression: \n"
            << expr.pretty() << eom;
    throw 0;
  }

  return empty_typet();
}

/// search known symbols from this scope up and return type, returning an
///   empty type if not found
typet rust_typecheckt::search_known_symbols(irep_idt const &symbol_name)
{
  irep_idt symbol_base_name = strip_to_base_name(symbol_name);

  int numScopes = static_cast<int>(known_symbols.size());

  for(int currScope = numScopes - 1; currScope >= 0; --currScope)
  {
    irep_idt prefixed_name =
      add_prefix(symbol_base_name, known_symbols[currScope].second);

    auto result = known_symbols[currScope].first.find(prefixed_name);
    if(result != known_symbols[currScope].first.end())
      return (*result).second;
  }

  return empty_typet();
}
/// search known symbols from this scope up and return type, returning an
///   empty id if not found
irep_idt
rust_typecheckt::find_existing_decorated_symbol(irep_idt const &symbol_name)
{
  irep_idt symbol_base_name = strip_to_base_name(symbol_name);

  int numScopes = static_cast<int>(known_symbols.size());

  for(int currScope = numScopes - 1; currScope >= 0; --currScope)
  {
    irep_idt prefixed_name =
      add_prefix(symbol_base_name, known_symbols[currScope].second);
    auto result = known_symbols[currScope].first.find(prefixed_name);
    if(result != known_symbols[currScope].first.end())
      return (*result).first;
  }

  return ID_empty;
}

/// Prefix parameters and variables with a procedure name
irep_idt rust_typecheckt::add_prefix(const irep_idt &ds)
{
  return id2string(proc_name) + "::" + std::to_string(scope_history.back()) +
         "::" + id2string(ds);
}

irep_idt rust_typecheckt::add_prefix(const irep_idt &ds, int passed_scope_level)
{
  return id2string(proc_name) + "::" + std::to_string(passed_scope_level) +
         "::" + id2string(ds);
}

irep_idt rust_typecheckt::strip_to_base_name(const irep_idt &original)
{
  std::string dest = id2string(original);

  std::string::size_type c_pos = dest.rfind("::");
  if(c_pos != std::string::npos)
    dest.erase(0, c_pos + 2);

  return dest;
}

typet rust_typecheckt::rust_reconcile_types(exprt &a, exprt &b)
{
  typet aType = a.type();
  typet bType = b.type();

  // Lookup variables from history
  if(is_empty_type(aType))
  {
    aType = lookup_type(a);
    a.type() = aType;
  }
  if(is_empty_type(bType))
  {
    bType = lookup_type(b);
    b.type() = bType;
  }

  if(aType == bType)
    return aType;
  else if(is_empty_type(aType))
    return bType;
  else if(is_empty_type(bType))
    return aType;
  else
  {
    // Handle differing types
    typet result = rust_resolve_differing_types(a, b);

    a.type() = result;
    b.type() = result;

    if(is_empty_type(result))
    {
      error() << "Unable to resolve types [" << aType.id() << "] and ["
              << bType.id() << "] from expressions:";
      error() << a.pretty() << "\n";
      error() << "and \n";
      error() << b.pretty() << "\n" << eom;

      throw 0;
    }

    return result;
  }
}

void rust_typecheckt::typecheck_expr_or_code(exprt &expr)
{
  if(expr.op0().type().id() == ID_code)
    typecheck_code(to_code(expr.op0()));
  else
    typecheck_expr(expr.op0());
}

void rust_typecheckt::update_expr_type(exprt &expr, const typet &type)
{
  expr.type() = type;

  if(expr.id() == ID_symbol)
  {
    const irep_idt &id = to_symbol_expr(expr).get_identifier();

    const auto maybe_symbol = symbol_table.get_writeable(id);
    if(!maybe_symbol)
    {
      error() << "unexpected symbol: " << id << eom;
      throw 0;
    }

    symbolt &s = *maybe_symbol;
    if(is_empty_type(s.type) || s.type.is_nil())
      s.type = type;
    else
      s.type = rust_union(s.type, type);
  }
}

void rust_typecheckt::make_type_compatible(
  exprt &expr,
  const typet &type,
  bool must)
{
  if(is_empty_type(type) || type.is_nil())
  {
    error().source_location = expr.source_location();
    error() << "make_type_compatible got empty type: " << expr.pretty() << eom;
    throw 0;
  }

  if(is_empty_type(expr.type()) || expr.type().is_nil())
  {
    // Type is not yet set
    update_expr_type(expr, type);
    return;
  }

  if(must)
  {
    if(rust_incompatible_types(expr.type(), type))
    {
      error().source_location = expr.source_location();
      error() << "failed to typecheck expr " << expr.pretty() << " with type "
              << expr.type().pretty() << "; required type " << type.pretty()
              << eom;
      throw 0;
    }
  }
  else if(!rust_is_subtype(type, expr.type()))
  {
    // Types are not compatible
    typet upper = rust_union(expr.type(), type);
    update_expr_type(expr, upper);
  }
}

void rust_typecheckt::typecheck_type(typet &type)
{
  if(type.id() == ID_code)
  {
    code_typet &parameters = to_code_type(type);

    for(code_typet::parametert &p : parameters.parameters())
    {
      // create new symbol
      parameter_symbolt new_symbol;
      new_symbol.base_name = strip_to_base_name(p.get_identifier());

      // append procedure name to parameters
      p.set_identifier(add_prefix(p.get_identifier()));
      new_symbol.name = p.get_identifier();

      new_symbol.type = p.type();

      /*if(is_rust_builtin_code_type(type))
        new_symbol.type = rust_value_or_empty_type();
      else if(is_rust_spec_code_type(type))
        new_symbol.type = rust_value_or_reference_type();
      else
        new_symbol.type = rust_value_type(); // User defined function*/

      known_symbols.back().first[add_prefix(new_symbol.base_name)] =
        new_symbol.type;

      new_symbol.mode = "rust";

      if(symbol_table.add(new_symbol))
      {
        error() << "failed to add parameter symbol `" << new_symbol.name
                << "' in the symbol table" << eom;
        throw 0;
      }
    }
  }
}

void rust_typecheckt::typecheck_loop(codet &code)
{
  irep_idt const &ID = code.get_statement();
  if(ID == ID_while)
  {
    code_whilet &loop = to_code_while(code);
    typecheck_expr(loop.cond());
    typecheck_code(loop.body());
  }
  else if(ID == ID_for)
  {
    // TODO only range based for loops, iterators and lists must be done first
  }
}

void rust_typecheckt::typecheck_expr(exprt &expr)
{
  // first do sub-nodes
  if(
    expr.id() !=
    ID_side_effect) // statement expressions must check their own sub-nodes
    typecheck_expr_operands(expr);

  // now do case-split
  typecheck_expr_main(expr);
}

void rust_typecheckt::typecheck_expr_operands(exprt &expr)
{
  Forall_operands(it, expr)
    typecheck_expr(*it);
}

void rust_typecheckt::typecheck_expr_main(exprt &expr)
{
  // unwrap code expressions
  if(expr.id() == ID_code)
  {
    // these are ok to be used as expressions, and they hold the expression
    //    in op0, so it's already been typechecked
    if(to_code(expr).get_statement() == ID_expression)
    {
    }
    else
    {
      error().source_location = expr.source_location();
      error() << "typecheck_expr_main got code: " << expr.pretty() << eom;
      throw 0;
    }
  }
  else if(expr.id() == ID_symbol)
    typecheck_symbol_expr(to_symbol_expr(expr));
  else if(expr.id() == ID_constant)
  {
  }
  else
  {
    if(
      expr.id() == ID_null || expr.id() == "undefined" || expr.id() == ID_empty)
    {
      typecheck_expr_constant(expr);
    }
    else if(
      expr.id() == "null_type" || expr.id() == "undefined_type" ||
      expr.id() == ID_boolean || expr.id() == ID_string ||
      expr.id() == "number" || expr.id() == "builtin_object" ||
      expr.id() == "user_object" || expr.id() == "object" ||
      expr.id() == ID_pointer || expr.id() == ID_member ||
      expr.id() == "variable")
    {
      expr.type() = rust_kind();
    }
    else if(
      expr.id() == "proto" || expr.id() == "fid" || expr.id() == "scope" ||
      expr.id() == "constructid" || expr.id() == "primvalue" ||
      expr.id() == "targetfunction" || expr.id() == ID_class)
    {
      // TO DO: have a special type for builtin fields
      expr.type() = string_typet();
    }
    else if(expr.id() == ID_not)
      typecheck_expr_unary_boolean(expr);
    else if(expr.id() == "string_to_num")
      typecheck_expr_unary_string(expr);
    else if(
      expr.id() == ID_unary_minus || expr.id() == "num_to_int32" ||
      expr.id() == "num_to_uint32" || expr.id() == ID_bitnot)
    {
      typecheck_expr_unary_num(expr);
    }
    else if(expr.id() == "num_to_string")
    {
      typecheck_expr_unary_num(expr);
      expr.type() = string_typet();
    }
    else if(expr.id() == ID_equal || expr.id() == ID_notequal)
      typecheck_exp_binary_equal(expr);
    else if(
      expr.id() == ID_lt || expr.id() == ID_le || expr.id() == ID_gt ||
      expr.id() == ID_ge)
    {
      typecheck_expr_binary_compare(expr);
    }
    else if(
      expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_mult ||
      expr.id() == ID_div || expr.id() == ID_mod || expr.id() == ID_bitand ||
      expr.id() == ID_bitor || expr.id() == ID_bitxor || expr.id() == ID_shl ||
      expr.id() == ID_shr || expr.id() == ID_lshr)
    {
      typecheck_expr_binary_arith(expr);
    }
    else if(expr.id() == ID_and || expr.id() == ID_or)
      typecheck_expr_binary_boolean(expr);
    else if(expr.id() == "subtype_of")
      typecheck_expr_subtype(expr);
    else if(expr.id() == ID_concatenation)
      typecheck_expr_concatenation(expr);
    else if(expr.id() == "ref")
      typecheck_expr_ref(expr);
    else if(expr.id() == "field")
      typecheck_expr_field(expr);
    else if(expr.id() == ID_base)
      typecheck_expr_base(expr);
    else if(expr.id() == ID_typeof)
      expr.type() = rust_kind();
    else if(expr.id() == "new")
      expr.type() = rust_user_object_type();
    else if(expr.id() == "hasField")
      typecheck_expr_has_field(expr);
    else if(expr.id() == ID_index)
      typecheck_expr_index(expr);
    else if(expr.id() == "delete")
      typecheck_expr_delete(expr);
    else if(expr.id() == "protoField")
      typecheck_expr_proto_field(expr);
    else if(expr.id() == "protoObj")
      typecheck_expr_proto_obj(expr);
    else if(expr.id() == ID_side_effect)
      typecheck_expr_side_effect(to_side_effect_expr(expr));
    else if(expr.id() == ID_address_of)
      typecheck_expr_address_of(to_address_of_expr(expr));
    else if(expr.id() == ID_dereference)
      typecheck_expr_dereference(to_dereference_expr(expr));
    else
    {
      error().source_location = expr.source_location();
      error() << "unexpected expression: " << expr.pretty() << eom;
      throw 0;
    }
  }
}

// COMP: assumes all returned types match as is required for Rust to compile
/// Recursively finds returned expressions, gathers the type, and replaces
///   them with assignment to a temporary
void process_side_effect_block(codet &code, symbol_exprt &temporary)
{
  if(code.get_statement() == ID_ifthenelse)
  {
    code_ifthenelset &ifelsestmt = to_code_ifthenelse(code);
    process_side_effect_block(ifelsestmt.then_case(), temporary);
    if(ifelsestmt.has_else_case())
      process_side_effect_block(ifelsestmt.else_case(), temporary);
    return;
  }

  code_blockt &block = to_code_block(code);

  for(auto &op : block.operands())
  {
    if(op.id() == ID_code && to_code(op).get_statement() == ID_ifthenelse)
    {
      code_ifthenelset &ifelsestmt = to_code_ifthenelse(to_code(op));
      process_side_effect_block(ifelsestmt.then_case(), temporary);
      if(ifelsestmt.has_else_case())
        process_side_effect_block(ifelsestmt.else_case(), temporary);
    }
    else if(op == block.operands().back())
    {
      if(to_code(op).get_statement() == ID_expression)
        op = code_assignt(temporary, op.op0());
    }
  }
}

typet extract_type_side_effect_block(codet &code)
{
  if(code.get_statement() == ID_ifthenelse)
  {
    code_ifthenelset &ifelsestmt = to_code_ifthenelse(code);
    typet a = extract_type_side_effect_block(ifelsestmt.then_case());
    if(!is_empty_type(a))
      return a;
    if(ifelsestmt.has_else_case())
    {
      typet a = extract_type_side_effect_block(ifelsestmt.else_case());
      if(!is_empty_type(a))
        return a;
    }
    return empty_typet();
  }

  code_blockt &processed_codeblock = to_code_block(code);

  for(auto &op : processed_codeblock.operands())
  {
    if(op.id() == ID_code && to_code(op).get_statement() == ID_ifthenelse)
    {
      code_ifthenelset &ifelsestmt = to_code_ifthenelse(to_code(op));
      typet a = extract_type_side_effect_block(ifelsestmt.then_case());
      if(!is_empty_type(a))
        return a;
      if(ifelsestmt.has_else_case())
      {
        typet a = extract_type_side_effect_block(ifelsestmt.else_case());
        if(!is_empty_type(a))
          return a;
      }
    }
    // assign statement to the created variable
    else if(op.id() == ID_code && to_code(op).get_statement() == ID_assign)
    {
      code_assignt assign = to_code_assign(to_code(op));
      if(
        assign.lhs().id() == ID_symbol &&
        id2string(to_symbol_expr(assign.lhs()).get_identifier())
            .find("typecheck_var--codeblock_expr_value") != std::string::npos)
      {
        return assign.rhs().type();
      }
    }
  }

  return empty_typet();
}

void rust_typecheckt::typecheck_expr_side_effect(side_effect_exprt &expr)
{
  if(expr.get_statement() == ID_function_call)
  {
    typecheck_function_call(expr);
  }
  else
  {
    code_blockt &original_codeblock = to_code_block(to_code(expr.op0()));

    // create processed code block wrapped in temporary to allow multiple
    //   returns via the temporary
    code_blockt processed_codeblock;
    symbol_exprt temporary(
      "typecheck_var--codeblock_expr_value", empty_typet());
    processed_codeblock.add(code_declt(temporary));
    processed_codeblock.append(original_codeblock);

    // process the block, getting the type and filling in the temporary
    process_side_effect_block(
      processed_codeblock, to_symbol_expr(processed_codeblock.op0().op0()));

    // add the true "return" of the temporary variable
    processed_codeblock.add(code_expressiont(temporary));

    // typecheck the processed codeblock
    expr.op0() = processed_codeblock;
    typecheck_block(to_code(expr.op0()));

    // determine block type
    typet returnType =
      extract_type_side_effect_block(to_code_block(to_code(expr.op0())));

    // set type of declared temp variable and declaration
    expr.op0().op0().op0().type() = returnType;
    expr.op0().op0().type() = returnType;
    // set type of returned temp variable and expression
    expr.op0().operands().back().op0().type() = returnType;
    expr.op0().operands().back().type() = returnType;

    // propogate type up to the expression level
    expr.op0().type() = expr.op0().op0().type();
    expr.type() = expr.op0().type();
  }
}

void rust_typecheckt::typecheck_expr_address_of(address_of_exprt &expr)
{
  expr.type() = pointer_type(expr.object().type());
}

void rust_typecheckt::typecheck_expr_dereference(dereference_exprt &expr)
{
  expr.type() = to_pointer_type(expr.pointer().type()).subtype();
}

void rust_typecheckt::typecheck_expr_constant(exprt &expr)
{
  if(expr.id() == ID_null)
    expr.type() = rust_null_type();
  else if(expr.id() == "undefined")
    expr.type() = rust_undefined_type();
  else if(expr.id() == ID_empty)
    expr.type() = rust_empty_type();
}

void rust_typecheckt::typecheck_expr_proto_field(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_object_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  expr.type() = rust_value_or_empty_type();
}

void rust_typecheckt::typecheck_expr_proto_obj(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands";
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_object_type(), true);
  make_type_compatible(expr.op1(), rust_object_type(), true);

  expr.type() = bool_typet();
}

void rust_typecheckt::typecheck_expr_delete(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_object_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  expr.type() = bool_typet();
}

void rust_typecheckt::typecheck_expr_index(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_object_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  // special case for function identifiers
  if(expr.op1().id() == "fid" || expr.op1().id() == "constructid")
    expr.type() = code_typet({}, empty_typet());
  else
    expr.type() = rust_value_type();
}

void rust_typecheckt::typecheck_expr_has_field(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_object_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  expr.type() = bool_typet();
}

void rust_typecheckt::typecheck_expr_field(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects single operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_reference_type(), true);

  expr.type() = string_typet();
}

void rust_typecheckt::typecheck_expr_base(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects single operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_reference_type(), true);

  expr.type() = rust_value_type();
}

void rust_typecheckt::typecheck_expr_ref(exprt &expr)
{
  if(expr.operands().size() != 3)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects three operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_value_type(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  exprt &operand3 = expr.op2();
  make_type_compatible(operand3, rust_kind(), true);

  if(operand3.id() == ID_member)
    expr.type() = rust_member_reference_type();
  else if(operand3.id() == "variable")
    expr.type() = rust_variable_reference_type();
  else
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id()
            << "' expects reference type in the third parameter. Got:"
            << operand3.pretty() << eom;
    throw 0;
  }
}

void rust_typecheckt::typecheck_expr_concatenation(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), string_typet(), true);
  make_type_compatible(expr.op1(), string_typet(), true);

  expr.type() = string_typet();
}

void rust_typecheckt::typecheck_expr_subtype(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), rust_kind(), true);
  make_type_compatible(expr.op1(), rust_kind(), true);

  expr.type() = bool_typet();
}

void rust_typecheckt::typecheck_expr_binary_boolean(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), bool_typet(), true);
  make_type_compatible(expr.op1(), bool_typet(), true);

  expr.type() = bool_typet();
}

void rust_typecheckt::typecheck_expr_binary_arith(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  // if float, use special float exprs
  if(
    expr.op0().type().id() == ID_floatbv ||
    expr.op1().type().id() == ID_floatbv)
  {
    irep_idt id;
    if(expr.id() == ID_plus)
      id = ID_floatbv_plus;
    else if(expr.id() == ID_minus)
      id = ID_floatbv_minus;
    else if(expr.id() == ID_mult)
      id = ID_floatbv_mult;
    else if(expr.id() == ID_div)
      id = ID_floatbv_div;
    else if(expr.id() == ID_mod)
      id = ID_floatbv_rem;

    expr = ieee_float_op_exprt(
      expr.op0(),
      id,
      expr.op1(),
      symbol_table
        .get_writeable_ref(std::string(CPROVER_PREFIX) + "rounding_mode")
        .symbol_expr());
  }

  typet newType = rust_reconcile_types(expr.op0(), expr.op1());
  expr.op0().type() = newType;
  expr.op1().type() = newType;
  expr.type() = newType;
}

void rust_typecheckt::typecheck_exp_binary_equal(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  typet resolved_type = rust_reconcile_types(expr.op0(), expr.op1());

  // if float, use special float exprs
  if(resolved_type.id() == ID_floatbv)
  {
    if(expr.id() == ID_equal)
      expr = ieee_float_equal_exprt(expr.op0(), expr.op1());
    else if(expr.id() == ID_notequal)
      expr = ieee_float_notequal_exprt(expr.op0(), expr.op1());
  }

  // operands can be of any types
  expr.type() = bool_typet();
}

void rust_typecheckt::typecheck_expr_binary_compare(exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects two operands" << eom;
    throw 0;
  }

  // type matching
  typet newType = rust_reconcile_types(expr.op0(), expr.op1());
  expr.op0().type() = newType;
  expr.op1().type() = newType;

  expr.type() = bool_typet();
}

void rust_typecheckt::typecheck_expr_unary_boolean(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects one operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), bool_typet(), true);

  expr.type() = bool_typet();
}

void rust_typecheckt::typecheck_expr_unary_string(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects one operand" << eom;
    throw 0;
  }

  make_type_compatible(expr.op0(), string_typet(), true);
}

void rust_typecheckt::typecheck_expr_unary_num(exprt &expr)
{
  if(expr.operands().size() != 1)
  {
    error().source_location = expr.source_location();
    error() << "operator `" << expr.id() << "' expects one operand" << eom;
    throw 0;
  }

  // get type if unknown
  if(is_empty_type(expr.op0().type()))
  {
    expr.op0().type() = search_known_symbols(expr.op0().id());
  }

  // Rust Boolean Not and Bitwise Not are the same symbol, so
  //   differentiation has to happen here
  if(expr.id() == ID_bitnot && expr.op0().type().id() == ID_bool)
  {
    expr = not_exprt(expr.op0());
    typecheck_expr_unary_boolean(expr);
  }
  else if(expr.op0().type().id() == ID_unsignedbv)
  {
    signedbv_typet signed_with_correct_width(
      to_unsignedbv_type(expr.op0().type()).get_width());
    exprt expr_with_correct_type("", signed_with_correct_width);
    expr.type() = rust_reconcile_types(expr_with_correct_type, expr.op0());
    return;
  }

  expr.type() = expr.op0().type();
}

void rust_typecheckt::typecheck_symbol_expr(symbol_exprt &symbol_expr)
{
  irep_idt identifier = symbol_expr.get_identifier();
  // if this is a variable, we need to check if we already
  // prefixed it and add to the symbol table if it is not there already
  irep_idt existing_decorated_symbol =
    find_existing_decorated_symbol(identifier);
  if(existing_decorated_symbol == ID_empty) // if symbol is not already known
  {
    error() << "Unknown symbol. It is either undeclared or not being added to "
               "rust_typecheckt::known_symbols: \n"
            << symbol_expr.pretty() << "\n"
            << eom;
    throw 0;
  }
  else
  {
    symbol_expr.type() = search_known_symbols(identifier);
    symbol_expr.set_identifier(existing_decorated_symbol);
  }
}

void rust_typecheckt::typecheck_code(codet &code)
{
  const irep_idt &statement = code.get_statement();

  if(statement == ID_function_call)
    typecheck_function_call(to_side_effect_expr(code));
  else if(statement == ID_return)
    typecheck_return(to_code_return(code));
  else if(statement == ID_expression)
  {
    if(code.operands().size() != 1)
    {
      error().source_location = code.source_location();
      error() << "expression statement expected to have one operand" << eom;
      throw 0;
    }

    typecheck_expr(code.op0());
    code.type() = code.op0().type();
  }
  else if(statement == ID_label)
  {
    typecheck_code(to_code_label(code).code());
  }
  else if(statement == ID_block)
    typecheck_block(code);
  else if(statement == ID_while || statement == ID_for)
  {
    typecheck_loop(code);
  }
  else if(statement == ID_ifthenelse)
    typecheck_ifthenelse(to_code_ifthenelse(code));
  else if(statement == ID_goto)
  {
  }
  else if(statement == ID_assign)
    typecheck_assign(to_code_assign(code));
  else if(statement == ID_try_catch)
    typecheck_try_catch(to_code_try_catch(code));
  else if(statement == ID_skip)
  {
  }
  else if(statement == ID_decl_block)
  {
    typecheck_decl_block(code);
  }
  else if(statement == ID_decl)
  {
    typecheck_decl(code);
  }
  else if(statement == ID_assert)
  {
    typecheck_expr(code.op0());
  }
  else if(statement == ID_assume)
  {
    typecheck_expr(code.op0());
  }
  else
  {
    /*error().source_location = code.source_location();
    error() << "unexpected statement: " << statement << eom;
    throw 0;*/
  }
}

void rust_typecheckt::typecheck_decl(codet &code_decl)
{
  if(code_decl.operands().size() != 1)
  {
    error() << "code_declt is expected to have 1 operand";
    throw 0;
  }

  code_declt &decl_expr = to_code_decl(code_decl);
  irep_idt identifier = to_symbol_expr(decl_expr.op0()).get_identifier();

  // if this is a variable, we need to check if we already
  // prefixed it and add to the symbol table if it is not there already
  irep_idt identifier_base = strip_to_base_name(identifier);
  if(!has_prefix(id2string(identifier), id2string(proc_name)))
  {
    identifier = add_prefix(identifier);
    to_symbol_expr(decl_expr.op0()).set_identifier(identifier);
  }

  symbol_tablet::symbolst::const_iterator s_it =
    symbol_table.symbols.find(identifier);

  if(s_it == symbol_table.symbols.end())
  {
    // create new symbol
    symbolt new_symbol;
    new_symbol.name = identifier;
    new_symbol.type = decl_expr.op0().type();
    new_symbol.base_name = identifier_base;
    new_symbol.mode = "rust";
    new_symbol.is_type = false;
    new_symbol.is_lvalue = new_symbol.type.id() != ID_code;

    if(symbol_table.add(new_symbol))
    {
      error() << "failed to add symbol `" << new_symbol.name
              << "' in the symbol table" << eom;
      throw 0;
    }
  }
  else
  {
    // TODO handle rust variable overwriting
    // symbol already exists
    // assert(!s_it->second.is_type);
    if(!s_it->second.is_type)
    {
      const symbolt &symbol = s_it->second;

      // type the expression
      decl_expr.type() = symbol.type;
    }
  }

  known_symbols.back().first[identifier] = decl_expr.op0().type();
}

void rust_typecheckt::typecheck_decl_block(codet &code_decl)
{
  if(code_decl.operands().size() != 2)
  {
    error() << "code ID_decl_block is expected to have 2 operands";
    throw 0;
  }

  // typecheck the assigned expression
  // typecheck rhs of assignment(lhs done after the declaration is checked)
  code_assignt &assignment = to_code_assign(to_code(code_decl.op1()));
  typecheck_expr(assignment.rhs());

  // if type is unspecified
  if(is_empty_type(code_decl.op0().op0().type()))
  {
    // new variable has the type of the assigned expression
    code_decl.op0().op0().type() = code_decl.op1().op1().type();
    // assignment has the type of the assigned expression
    code_decl.op1().type() = code_decl.op1().op1().type();
  }
  else
  {
    // assignment has the type of the new variable
    code_decl.op1().type() = code_decl.op0().op0().type();
  }

  // add the new variable to the symbol table
  typecheck_decl(to_code(code_decl.op0()));

  // typecheck the lefthand side of the assignment
  typecheck_expr(assignment.lhs());

  typet resolved_type =
    rust_reconcile_types(assignment.lhs(), assignment.rhs());
  make_type_compatible(assignment.lhs(), resolved_type, false);
}

void rust_typecheckt::typecheck_return(code_returnt &code)
{
  if(code.has_return_value())
  {
    typecheck_expr(code.return_value());

    // COMP: assumes return type is typecastable into function return type,
    //   or the Rust code wouldn't compile
    // TODO: If proc_name ends up being more than the function name, change
    //   this. The if check can be removed entirely, but then unnecessary
    //   typecasting would be done
    typet func_type =
      to_code_type(symbol_table.lookup_ref(proc_name).type).return_type();
    if(func_type != code.return_value().type())
      code.return_value() = typecast_exprt(code.return_value(), func_type);
  }
}

void rust_typecheckt::typecheck_block(codet &code)
{
  scope_history.push_back(++max_scope);
  known_symbols.push_back(std::make_pair(
    std::unordered_map<irep_idt, typet>(), scope_history.back()));

  Forall_operands(it, code)
    typecheck_code(to_code(*it));

  known_symbols.pop_back();
  scope_history.pop_back();
}

void rust_typecheckt::typecheck_try_catch(code_try_catcht &code)
{
  // A special case of try catch with one catch clause
  if(code.operands().size() != 3)
  {
    error().source_location = code.source_location();
    error() << "try_catch expected to have three operands" << eom;
    throw 0;
  }

  // function call
  typecheck_function_call(to_side_effect_expr(code.try_code()));

  // catch decl is not used, but is required by goto-programs

  typecheck_code(code.get_catch_code(0));
}

void rust_typecheckt::typecheck_function_call(side_effect_exprt &expr)
{
  if(expr.operands().size() != 2)
  {
    error() << "function call expected to have two operands\n"
            << expr.pretty() << eom;
    throw 0;
  }

  expr.type() = lookup_type(expr);
  to_code_type(expr.op0().type()).return_type() = expr.type();

  exprt &args = expr.op1();
  for(auto &arg : args.operands())
    typecheck_expr(arg);

  code_typet::parameterst &params =
    to_code_type(expr.op0().type()).parameters();
  for(auto &param : params)
  {
    typecheck_expr(param.op0());
    param.type() = param.op0().type();
  }
}

void rust_typecheckt::typecheck_ifthenelse(code_ifthenelset &code)
{
  exprt &cond = code.cond();
  typecheck_expr(cond);
  make_type_compatible(cond, bool_typet(), true);

  typecheck_code(code.then_case());

  if(!code.else_case().is_nil())
    typecheck_code(code.else_case());
}

void rust_typecheckt::typecheck_assign(code_assignt &code)
{
  typecheck_expr(code.lhs());
  typecheck_expr(code.rhs());
  typet resolved_type = rust_reconcile_types(code.lhs(), code.rhs());
  make_type_compatible(code.lhs(), resolved_type, false);
  code.type() = resolved_type;
}

/// typechecking procedure declaration; any other symbols should have been
/// typechecked during typechecking of procedure declaration
/// \par parameters: any symbol
void rust_typecheckt::typecheck_non_type_symbol(symbolt &symbol)
{
  scope_history.push_back(++max_scope);
  known_symbols.push_back(std::make_pair(
    std::unordered_map<irep_idt, typet>(), scope_history.back()));

  // assert(!symbol.is_type);
  if(symbol.is_type)
  {
    throw 0;
  }

  proc_name = symbol.name;
  typecheck_type(symbol.type);

  if(symbol.value.id() == ID_code)
    typecheck_code(to_code(symbol.value));
  else if(symbol.value.is_nil())
  {
  }
  else
  {
    error().source_location = symbol.location;
    error() << "non-type symbol value expected code, but got "
            << symbol.value.pretty() << eom;
    throw 0;
  }

  known_symbols.pop_back();
  scope_history.pop_back();
}

void rust_typecheckt::typecheck()
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
    symbolt &symbol = symbol_table.get_writeable_ref(id);
    if(symbol.is_type)
      typecheck_type_symbol(symbol);
  }

  // We now check all non-type symbols
  for(const irep_idt &id : identifiers)
  {
    symbolt &symbol = symbol_table.get_writeable_ref(id);
    if(!symbol.is_type)
      typecheck_non_type_symbol(symbol);
  }
}

bool rust_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  rust_typecheckt rust_typecheck(symbol_table, message_handler);
  return rust_typecheck.typecheck_main();
}

bool rust_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &)
{
  const unsigned errors_before =
    message_handler.get_message_count(messaget::M_ERROR);

  symbol_tablet symbol_table;

  rust_typecheckt rust_typecheck(symbol_table, message_handler);

  try
  {
    rust_typecheck.typecheck_expr(expr);
  }

  catch(int)
  {
    rust_typecheck.error();
  }

  catch(const char *e)
  {
    rust_typecheck.error() << e << messaget::eom;
  }

  catch(const std::string &e)
  {
    rust_typecheck.error() << e << messaget::eom;
  }

  return message_handler.get_message_count(messaget::M_ERROR) != errors_before;
}
