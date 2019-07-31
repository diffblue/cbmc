/*******************************************************************\

Module: Statement List Language Type Checking

Author: Matthias Weiss, matthias.weiss@diffblue.com

\*******************************************************************/

/// \file
/// Statement List Language Type Checking

#include "statement_list_typecheck.h"
#include "converters/statement_list_types.h"

#include <iostream>
#include <util/ieee_float.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

/// Size of pointers in Siemens TIA.
#define STATEMENT_LIST_PTR_WIDTH 64
// TODO: Replace with more specific exception throws.
#define TYPECHECK_ERROR 0
/// Artificial name for the data block interface of a function block.
#define DATA_BLOCK_PARAMETER_NAME "data_block"
/// Postfix for the type of a data block.
#define DATA_BLOCK_TYPE_POSTFIX "_db"
/// Name of the CBMC assert function.
#define CPROVER_ASSERT CPROVER_PREFIX "assert"
/// Name of the CBMC assume function.
#define CPROVER_ASSUME CPROVER_PREFIX "assume"
/// Name of the RLO symbol used in some operations.
#define CPROVER_TEMP_RLO CPROVER_PREFIX "temp_rlo"

/// Creates the artificial data block parameter with a generic name and the
/// specified type.
/// \param data_block_type: Type of the data block.
/// \param function_block_name: Name of the function block to which this data
///   block belongs.
/// \return Parameter of the data block.
static code_typet::parametert create_data_block_parameter(
  const struct_typet &data_block_type,
  const irep_idt &function_block_name)
{
  const pointer_typet db_ptr{data_block_type, STATEMENT_LIST_PTR_WIDTH};
  code_typet::parametert param{db_ptr};
  param.set_identifier(
    id2string(function_block_name) + "::" + DATA_BLOCK_PARAMETER_NAME);
  param.set_base_name(DATA_BLOCK_PARAMETER_NAME);
  return param;
}

bool statement_list_typecheck(
  const statement_list_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
{
  statement_list_typecheckt stl_typecheck(
    parse_tree, symbol_table, module, message_handler);

  return stl_typecheck.typecheck_main();
}

statement_list_typecheckt::nesting_stack_entryt::nesting_stack_entryt(
  exprt rlo_bit,
  bool or_bit,
  codet function_code)
  : rlo_bit(rlo_bit), or_bit(or_bit), function_code(function_code)
{
}

statement_list_typecheckt::statement_list_typecheckt(
  const statement_list_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  const std::string &module,
  message_handlert &message_handler)
  : typecheckt(message_handler),
    parse_tree(parse_tree),
    symbol_table(symbol_table),
    module(module)
{
}

void statement_list_typecheckt::typecheck()
{
  // First fill the symbol table with function, tag and parameter declarations
  // to be able to properly resolve block calls later.
  for(const statement_list_parse_treet::functiont &fc : parse_tree.functions)
    typecheck_function_declaration(fc);
  for(const statement_list_parse_treet::function_blockt &fb :
      parse_tree.function_blocks)
    typecheck_function_block_declaration(fb);
  typecheck_tag_list();
  // Temporary RLO symbol for certain operations.
  add_temp_rlo();

  // Iterate through all networks to generate the function bodies.
  for(const statement_list_parse_treet::function_blockt &fb :
      parse_tree.function_blocks)
  {
    symbolt &fb_sym{symbol_table.get_writeable_ref(fb.name)};
    typecheck_statement_list_networks(fb, fb_sym);
  }
  for(const statement_list_parse_treet::functiont &fc : parse_tree.functions)
  {
    symbolt &function_sym{symbol_table.get_writeable_ref(fc.name)};
    typecheck_statement_list_networks(fc, function_sym);
  }
}

void statement_list_typecheckt::typecheck_function_block_declaration(
  const statement_list_parse_treet::function_blockt &function_block)
{
  // Create FB symbol.
  symbolt function_block_sym;
  function_block_sym.module = module;
  function_block_sym.name = function_block.name;
  function_block_sym.base_name = function_block_sym.name;
  function_block_sym.pretty_name = function_block_sym.name;
  function_block_sym.mode = ID_statement_list;

  // When calling function blocks, the passed parameters are value-copied to a
  // corresponding instance data block. This block contains all input, inout,
  // output and static variables. The function block reads and writes only
  // those fields and does not modify the actual parameters. To simulate this
  // behaviour, all function blocks are modeled as functions with a single
  // parameter: An instance of their data block, whose members they modify.

  // Create and add DB type symbol.
  const struct_typet data_block_type{
    create_instance_data_block_type(function_block)};
  type_symbolt data_block{data_block_type};
  data_block.name =
    id2string(function_block_sym.name) + DATA_BLOCK_TYPE_POSTFIX;
  data_block.base_name = data_block.name;
  data_block.mode = ID_statement_list;
  symbol_table.add(data_block);

  // Create and add parameter symbol.
  code_typet::parametert param{
    create_data_block_parameter(data_block_type, function_block_sym.name)};
  parameter_symbolt param_sym;
  param_sym.module = module;
  param_sym.type = param.type();
  param_sym.name = param.get_identifier();
  param_sym.base_name = DATA_BLOCK_PARAMETER_NAME;
  param_sym.pretty_name = param_sym.base_name;
  param_sym.mode = ID_statement_list;
  symbol_table.add(param_sym);

  // Setup FB symbol type and value.
  code_typet::parameterst params;
  params.push_back(param);
  code_typet fb_type{params, empty_typet()};
  fb_type.set(ID_statement_list_type, ID_statement_list_function_block);
  function_block_sym.type = fb_type;
  symbol_table.add(function_block_sym);
}

void statement_list_typecheckt::typecheck_function_declaration(
  const statement_list_parse_treet::functiont &function)
{
  symbolt function_sym;
  function_sym.module = module;
  function_sym.name = function.name;
  function_sym.base_name = function_sym.name;
  function_sym.pretty_name = function_sym.name;
  function_sym.mode = ID_statement_list;
  code_typet::parameterst params;
  typecheck_function_var_decls(
    function.var_input, params, function.name, ID_statement_list_var_input);
  typecheck_function_var_decls(
    function.var_inout, params, function.name, ID_statement_list_var_inout);
  typecheck_function_var_decls(
    function.var_output, params, function.name, ID_statement_list_var_output);

  code_typet fc_type{params, function.return_type};
  fc_type.set(ID_statement_list_type, ID_statement_list_function);
  function_sym.type = fc_type;
  symbol_table.add(function_sym);
}

void statement_list_typecheckt::typecheck_tag_list()
{
  for(const symbol_exprt &tag : parse_tree.tags)
  {
    symbolt tag_sym;
    tag_sym.is_static_lifetime = true;
    tag_sym.module = module;
    tag_sym.name = tag.get_identifier();
    tag_sym.base_name = tag_sym.name;
    tag_sym.pretty_name = tag_sym.name;
    tag_sym.type = tag.type();
    tag_sym.mode = ID_statement_list;
    symbol_table.add(tag_sym);
  }
}

void statement_list_typecheckt::add_temp_rlo()
{
  symbolt temp_rlo;
  temp_rlo.is_static_lifetime = true;
  temp_rlo.module = module;
  temp_rlo.name = CPROVER_TEMP_RLO;
  temp_rlo.base_name = temp_rlo.name;
  temp_rlo.pretty_name = temp_rlo.name;
  temp_rlo.type = get_bool_type();
  temp_rlo.mode = ID_statement_list;
  symbol_table.add(temp_rlo);
}

struct_typet statement_list_typecheckt::create_instance_data_block_type(
  const statement_list_parse_treet::function_blockt &function_block)
{
  struct_union_typet::componentst components;
  typecheck_function_block_var_decls(
    function_block.var_input, components, ID_statement_list_var_input);
  typecheck_function_block_var_decls(
    function_block.var_inout, components, ID_statement_list_var_inout);
  typecheck_function_block_var_decls(
    function_block.var_output, components, ID_statement_list_var_output);
  typecheck_function_block_var_decls(
    function_block.var_static, components, ID_statement_list_var_static);

  return struct_typet{components};
}

void statement_list_typecheckt::typecheck_function_block_var_decls(
  const statement_list_parse_treet::var_declarationst &var_decls,
  struct_union_typet::componentst &components,
  const irep_idt &var_property)
{
  for(const statement_list_parse_treet::var_declarationt &declaration :
      var_decls)
  {
    const irep_idt &var_name{declaration.variable.get_identifier()};
    const typet &var_type{declaration.variable.type()};
    struct_union_typet::componentt component{var_name, var_type};
    component.set(ID_statement_list_type, var_property);
    components.push_back(component);
  }
}

void statement_list_typecheckt::typecheck_function_var_decls(
  const statement_list_parse_treet::var_declarationst &var_decls,
  code_typet::parameterst &params,
  const irep_idt &function_name,
  const irep_idt &var_property)
{
  for(const statement_list_parse_treet::var_declarationt &declaration :
      var_decls)
  {
    parameter_symbolt param_sym;
    param_sym.module = module;
    param_sym.type = declaration.variable.type();
    param_sym.name = id2string(function_name) +
                     "::" + id2string(declaration.variable.get_identifier());
    param_sym.base_name = declaration.variable.get_identifier();
    param_sym.pretty_name = param_sym.base_name;
    param_sym.mode = ID_statement_list;
    symbol_table.add(param_sym);

    code_typet::parametert param{declaration.variable.type()};
    param.set_identifier(param_sym.name);
    param.set_base_name(declaration.variable.get_identifier());
    param.set(ID_statement_list_type, var_property);
    params.push_back(param);
  }
}

void statement_list_typecheckt::typecheck_temp_var_decls(
  const statement_list_parse_treet::tia_modulet &tia_module,
  symbolt &tia_symbol)
{
  for(const statement_list_parse_treet::var_declarationt &declaration :
      tia_module.var_temp)
  {
    symbolt temp_sym;
    temp_sym.name = id2string(tia_symbol.name) +
                    "::" + id2string(declaration.variable.get_identifier());
    temp_sym.base_name = declaration.variable.get_identifier();
    temp_sym.pretty_name = temp_sym.base_name;
    temp_sym.type = declaration.variable.type();
    temp_sym.mode = ID_statement_list;
    temp_sym.module = module;
    symbol_table.add(temp_sym);

    const code_declt code_decl{temp_sym.symbol_expr()};
    tia_symbol.value.add_to_operands(code_decl);
  }
}

void statement_list_typecheckt::typecheck_statement_list_networks(
  const statement_list_parse_treet::tia_modulet &tia_module,
  symbolt &tia_symbol)
{
  // Leave value empty if there are no networks to iterate through.
  if(tia_module.networks.empty())
    return;
  if(tia_symbol.value.is_nil())
    tia_symbol.value = code_blockt{};

  typecheck_temp_var_decls(tia_module, tia_symbol);

  for(const auto &network : tia_module.networks)
  {
    // Set RLO to true each time a new network is entered (TIA behaviour).
    rlo_bit = true_exprt();
    for(const auto &instruction : network.instructions)
      typecheck_statement_list_instruction(instruction, tia_symbol);
  }
}

void statement_list_typecheckt::typecheck_statement_list_instruction(
  const statement_list_parse_treet::instructiont &instruction,
  symbolt &tia_element)
{
  const codet &op_code{instruction.tokens.back()};
  const irep_idt statement{op_code.get_statement()};

  if(ID_statement_list_load == statement)
    typecheck_statement_list_load(op_code, tia_element);
  else if(ID_statement_list_transfer == statement)
    typecheck_statement_list_transfer(op_code, tia_element);
  else if(ID_statement_list_accu_int_add == statement)
    typecheck_statement_list_accu_int_add(op_code);
  else if(ID_statement_list_accu_int_sub == statement)
    typecheck_statement_list_accu_int_sub(op_code);
  else if(ID_statement_list_accu_int_mul == statement)
    typecheck_statement_list_accu_int_mul(op_code);
  else if(ID_statement_list_accu_int_div == statement)
    typecheck_statement_list_accu_int_div(op_code);
  else if(ID_statement_list_accu_int_eq == statement)
    typecheck_statement_list_accu_int_eq(op_code);
  else if(ID_statement_list_accu_int_neq == statement)
    typecheck_statement_list_accu_int_neq(op_code);
  else if(ID_statement_list_accu_int_lt == statement)
    typecheck_statement_list_accu_int_lt(op_code);
  else if(ID_statement_list_accu_int_gt == statement)
    typecheck_statement_list_accu_int_gt(op_code);
  else if(ID_statement_list_accu_int_lte == statement)
    typecheck_statement_list_accu_int_lte(op_code);
  else if(ID_statement_list_accu_int_gte == statement)
    typecheck_statement_list_accu_int_gte(op_code);
  else if(ID_statement_list_accu_dint_add == statement)
    typecheck_statement_list_accu_dint_add(op_code);
  else if(ID_statement_list_accu_dint_sub == statement)
    typecheck_statement_list_accu_dint_sub(op_code);
  else if(ID_statement_list_accu_dint_mul == statement)
    typecheck_statement_list_accu_dint_mul(op_code);
  else if(ID_statement_list_accu_dint_div == statement)
    typecheck_statement_list_accu_dint_div(op_code);
  else if(ID_statement_list_accu_dint_eq == statement)
    typecheck_statement_list_accu_dint_eq(op_code);
  else if(ID_statement_list_accu_dint_neq == statement)
    typecheck_statement_list_accu_dint_neq(op_code);
  else if(ID_statement_list_accu_dint_lt == statement)
    typecheck_statement_list_accu_dint_lt(op_code);
  else if(ID_statement_list_accu_dint_gt == statement)
    typecheck_statement_list_accu_dint_gt(op_code);
  else if(ID_statement_list_accu_dint_lte == statement)
    typecheck_statement_list_accu_dint_lte(op_code);
  else if(ID_statement_list_accu_dint_gte == statement)
    typecheck_statement_list_accu_dint_gte(op_code);
  else if(ID_statement_list_accu_real_add == statement)
    typecheck_statement_list_accu_real_add(op_code);
  else if(ID_statement_list_accu_real_sub == statement)
    typecheck_statement_list_accu_real_sub(op_code);
  else if(ID_statement_list_accu_real_mul == statement)
    typecheck_statement_list_accu_real_mul(op_code);
  else if(ID_statement_list_accu_real_div == statement)
    typecheck_statement_list_accu_real_div(op_code);
  else if(ID_statement_list_accu_real_eq == statement)
    typecheck_statement_list_accu_real_eq(op_code);
  else if(ID_statement_list_accu_real_neq == statement)
    typecheck_statement_list_accu_real_neq(op_code);
  else if(ID_statement_list_accu_real_lt == statement)
    typecheck_statement_list_accu_real_lt(op_code);
  else if(ID_statement_list_accu_real_gt == statement)
    typecheck_statement_list_accu_real_gt(op_code);
  else if(ID_statement_list_accu_real_lte == statement)
    typecheck_statement_list_accu_real_lte(op_code);
  else if(ID_statement_list_accu_real_gte == statement)
    typecheck_statement_list_accu_real_gte(op_code);
  else if(ID_statement_list_not == statement)
    typecheck_statement_list_not(op_code);
  else if(ID_statement_list_and == statement)
    typecheck_statement_list_and(op_code, tia_element);
  else if(ID_statement_list_and_not == statement)
    typecheck_statement_list_and_not(op_code, tia_element);
  else if(ID_statement_list_or == statement)
    typecheck_statement_list_or(op_code, tia_element);
  else if(ID_statement_list_or_not == statement)
    typecheck_statement_list_or_not(op_code, tia_element);
  else if(ID_statement_list_xor == statement)
    typecheck_statement_list_xor(op_code, tia_element);
  else if(ID_statement_list_xor_not == statement)
    typecheck_statement_list_xor_not(op_code, tia_element);
  else if(ID_statement_list_and_nested == statement)
    typecheck_statement_list_nested_and(op_code);
  else if(ID_statement_list_and_not_nested == statement)
    typecheck_statement_list_nested_and_not(op_code);
  else if(ID_statement_list_or_nested == statement)
    typecheck_statement_list_nested_or(op_code);
  else if(ID_statement_list_or_not_nested == statement)
    typecheck_statement_list_nested_or_not(op_code);
  else if(ID_statement_list_xor_nested == statement)
    typecheck_statement_list_nested_xor(op_code);
  else if(ID_statement_list_xor_not_nested == statement)
    typecheck_statement_list_nested_xor_not(op_code);
  else if(ID_statement_list_nesting_closed == statement)
    typecheck_statement_list_nesting_closed(op_code);
  else if(ID_statement_list_assign == statement)
    typecheck_statement_list_assign(op_code, tia_element);
  else if(ID_statement_list_set_rlo == statement)
    typecheck_statement_list_set_rlo(op_code);
  else if(ID_statement_list_clr_rlo == statement)
    typecheck_statement_list_clr_rlo(op_code);
  else if(ID_statement_list_set == statement)
    typecheck_statement_list_set(op_code, tia_element);
  else if(ID_statement_list_reset == statement)
    typecheck_statement_list_reset(op_code, tia_element);
  else if(ID_statement_list_nop == statement)
    return;
  else if(ID_statement_list_call == statement)
    typecheck_statement_list_call(op_code, tia_element);
  else
  {
    error() << "OP code of instruction not found: " << op_code.get_statement()
            << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_statement_list_load(
  const codet &op_code,
  const symbolt &tia_element)
{
  const symbol_exprt *const symbol =
    expr_try_dynamic_cast<symbol_exprt>(op_code.op0());
  if(symbol)
  {
    const irep_idt &identifier{symbol->get_identifier()};
    const exprt val{typecheck_identifier(tia_element, identifier)};
    accumulator.push_back(val);
  }
  else if(can_cast_expr<constant_exprt>(op_code.op0()))
    accumulator.push_back(op_code.op0());
  else
  {
    error() << "Instruction is not followed by symbol or constant" << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_statement_list_transfer(
  const codet &op_code,
  symbolt &tia_element)
{
  const symbol_exprt &op{typecheck_instruction_with_non_const_operand(op_code)};
  const exprt lhs{typecheck_identifier(tia_element, op.get_identifier())};
  if(lhs.type() != accumulator.back().type())
  {
    error() << "Types of transfer assignment do not match" << eom;
    throw TYPECHECK_ERROR;
  }
  const code_assignt assignment{lhs, accumulator.back()};
  tia_element.value.add_to_operands(assignment);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_add(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const plus_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_sub(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const minus_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_mul(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const mult_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_div(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const div_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_eq(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_equal);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_neq(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_notequal);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_lt(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_lt);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_gt(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_gt);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_lte(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_le);
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_gte(
  const codet &op_code)
{
  typecheck_statement_list_accu_int_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_ge);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_add(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const plus_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_sub(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const minus_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_mul(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const mult_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_div(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const div_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_eq(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_equal);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_neq(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_notequal);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_lt(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_lt);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_gt(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_gt);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_lte(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_le);
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_gte(
  const codet &op_code)
{
  typecheck_statement_list_accu_dint_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_ge);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_add(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const plus_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_sub(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const minus_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_mul(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const mult_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_div(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);

  // Pop first operand, peek second.
  const exprt accu1{accumulator.back()};
  accumulator.pop_back();
  const exprt &accu2{accumulator.back()};
  const div_exprt operation{accu2, accu1};
  accumulator.push_back(operation);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_eq(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_equal);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_neq(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_notequal);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_lt(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_lt);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_gt(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_gt);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_lte(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_le);
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_gte(
  const codet &op_code)
{
  typecheck_statement_list_accu_real_arith(op_code);
  typecheck_accumulator_compare_instruction(ID_ge);
}

void statement_list_typecheckt::typecheck_statement_list_not(
  const codet &op_code)
{
  typecheck_instruction_without_operand(op_code);
  if(fc_bit)
  {
    const not_exprt unsimplified{rlo_bit};
    rlo_bit = simplify_expr(unsimplified, namespacet(symbol_table));
    or_bit = false;
  }
  else
    initialize_bit_expression(false_exprt{});
}

void statement_list_typecheckt::typecheck_statement_list_and(
  const codet &op_code,
  const symbolt &tia_element)
{
  exprt op{
    typecheck_simple_boolean_instruction_operand(op_code, tia_element, false)};

  // If inside of a bit string and if the OR bit is not set, create an 'and'
  // expression with the operand and the current contents of the rlo bit. If
  // the OR bit is set then this instruction is part of an 'and-before-or'
  // block and needs to be added to the rlo in a special way.
  if(fc_bit && or_bit)
    add_to_or_rlo_wrapper(op);
  else if(fc_bit)
  {
    const and_exprt unsimplified{rlo_bit, op};
    rlo_bit = simplify_expr(unsimplified, namespacet(symbol_table));
  }
  else
    initialize_bit_expression(op);
}

void statement_list_typecheckt::typecheck_statement_list_and_not(
  const codet &op_code,
  const symbolt &tia_element)
{
  exprt op{
    typecheck_simple_boolean_instruction_operand(op_code, tia_element, true)};

  // If inside of a bit string and if the OR bit is not set, create an 'and'
  // expression with the operand and the current contents of the rlo bit. If
  // the OR bit is set then this instruction is part of an 'and-before-or'
  // block and needs to be added to the rlo in a special way.
  if(or_bit && fc_bit)
    add_to_or_rlo_wrapper(op);
  else if(fc_bit)
  {
    const and_exprt unsimplified{rlo_bit, op};
    rlo_bit = simplify_expr(unsimplified, namespacet(symbol_table));
  }
  else
    initialize_bit_expression(op);
}

void statement_list_typecheckt::typecheck_statement_list_or(
  const codet &op_code,
  const symbolt &tia_element)
{
  if(op_code.operands().empty())
  {
    typecheck_statement_list_and_before_or();
    return;
  }
  const symbol_exprt &sym{
    typecheck_instruction_with_non_const_operand(op_code)};
  const exprt op{typecheck_identifier(tia_element, sym.get_identifier())};

  // If inside of a bit string, create an 'or' expression with the operand and
  // the current contents of the rlo bit.
  if(fc_bit)
  {
    const or_exprt unsimplified{rlo_bit, op};
    rlo_bit = simplify_expr(unsimplified, namespacet(symbol_table));
    or_bit = false;
  }
  else
    initialize_bit_expression(op);
}

void statement_list_typecheckt::typecheck_statement_list_or_not(
  const codet &op_code,
  const symbolt &tia_element)
{
  const symbol_exprt &sym{
    typecheck_instruction_with_non_const_operand(op_code)};
  const exprt op{typecheck_identifier(tia_element, sym.get_identifier())};
  const not_exprt not_op{op};

  // If inside of a bit string, create an 'or' expression with the operand and
  // the current contents of the rlo bit.
  if(fc_bit)
  {
    const or_exprt unsimplified{rlo_bit, not_op};
    rlo_bit = simplify_expr(unsimplified, namespacet(symbol_table));
    or_bit = false;
  }
  else
    initialize_bit_expression(not_op);
}

void statement_list_typecheckt::typecheck_statement_list_xor(
  const codet &op_code,
  const symbolt &tia_element)
{
  const symbol_exprt &sym{
    typecheck_instruction_with_non_const_operand(op_code)};
  const exprt op{typecheck_identifier(tia_element, sym.get_identifier())};

  // If inside of a bit string, create an 'xor' expression with the operand and
  // the current contents of the rlo bit.
  if(fc_bit)
  {
    const xor_exprt unsimplified{rlo_bit, op};
    rlo_bit = simplify_expr(unsimplified, namespacet(symbol_table));
    or_bit = false;
  }
  else
    initialize_bit_expression(op);
}

void statement_list_typecheckt::typecheck_statement_list_xor_not(
  const codet &op_code,
  const symbolt &tia_element)
{
  const symbol_exprt &sym{
    typecheck_instruction_with_non_const_operand(op_code)};
  const exprt op{typecheck_identifier(tia_element, sym.get_identifier())};
  const not_exprt not_op{op};

  // If inside of a bit string, create an 'xor not' expression with the
  // operand and the current contents of the rlo bit.
  if(fc_bit)
  {
    const xor_exprt unsimplified{rlo_bit, not_op};
    rlo_bit = simplify_expr(unsimplified, namespacet(symbol_table));
    or_bit = false;
  }
  else
    initialize_bit_expression(not_op);
}

void statement_list_typecheckt::typecheck_statement_list_and_before_or()
{
  if(fc_bit)
  {
    rlo_bit = or_exprt{rlo_bit, false_exprt{}};
    or_bit = true;
  }
  else
    return; // Instruction has no semantic influence.
}

void statement_list_typecheckt::typecheck_statement_list_nested_and(
  const codet &op_code)
{
  // Set the rlo to true implicitly so that the value of the AND instruction
  // is being loaded in case of a new bit string.
  typecheck_nested_boolean_instruction(op_code, true_exprt{});
}

void statement_list_typecheckt::typecheck_statement_list_nested_and_not(
  const codet &op_code)
{
  // Set the rlo to true implicitly so that the value of the AND instruction
  // is being loaded in case of a new bit string.
  typecheck_nested_boolean_instruction(op_code, true_exprt{});
}

void statement_list_typecheckt::typecheck_statement_list_nested_or(
  const codet &op_code)
{
  // Set the rlo to false implicitly so that the value of the OR instruction
  // is being loaded in case of a new bit string.
  typecheck_nested_boolean_instruction(op_code, false_exprt{});
}

void statement_list_typecheckt::typecheck_statement_list_nested_or_not(
  const codet &op_code)
{
  // Set the rlo to false implicitly so that the value of the OR instruction
  // is being loaded in case of a new bit string.
  typecheck_nested_boolean_instruction(op_code, false_exprt{});
}

void statement_list_typecheckt::typecheck_statement_list_nested_xor(
  const codet &op_code)
{
  // Set the rlo to false implicitly so that the value of the XOR instruction
  // is being loaded in case of a new bit string.
  typecheck_nested_boolean_instruction(op_code, false_exprt{});
}

void statement_list_typecheckt::typecheck_statement_list_nested_xor_not(
  const codet &op_code)
{
  // Set the rlo to false implicitly so that the value of the XOR instruction
  // is being loaded in case of a new bit string.
  typecheck_nested_boolean_instruction(op_code, false_exprt{});
}

void statement_list_typecheckt::typecheck_statement_list_nesting_closed(
  const codet &op_code)
{
  typecheck_instruction_without_operand(op_code);
  if(nesting_stack.empty())
  {
    error() << "Wrong order of brackets (Right parenthesis is not preceded by "
               "nesting)"
            << eom;
    throw TYPECHECK_ERROR;
  }
  or_bit = nesting_stack.back().or_bit;
  fc_bit = true;
  const irep_idt &statement{nesting_stack.back().function_code.get_statement()};
  if(ID_statement_list_and_nested == statement)
  {
    if(or_bit)
    {
      const exprt op{rlo_bit};
      rlo_bit = nesting_stack.back().rlo_bit;
      add_to_or_rlo_wrapper(op);
    }
    else
      rlo_bit = and_exprt{nesting_stack.back().rlo_bit, rlo_bit};
  }
  else if(ID_statement_list_and_not_nested == statement)
  {
    if(or_bit)
    {
      const not_exprt op{rlo_bit};
      rlo_bit = nesting_stack.back().rlo_bit;
      add_to_or_rlo_wrapper(op);
    }
    else
      rlo_bit = and_exprt{nesting_stack.back().rlo_bit, not_exprt{rlo_bit}};
  }
  else if(ID_statement_list_or_nested == statement)
  {
    or_bit = false;
    rlo_bit = or_exprt{nesting_stack.back().rlo_bit, rlo_bit};
  }
  else if(ID_statement_list_or_not_nested == statement)
  {
    or_bit = false;
    rlo_bit = or_exprt{nesting_stack.back().rlo_bit, not_exprt{rlo_bit}};
  }
  else if(ID_statement_list_xor_nested == statement)
  {
    or_bit = false;
    rlo_bit = xor_exprt{nesting_stack.back().rlo_bit, rlo_bit};
  }
  else if(ID_statement_list_xor_not_nested == statement)
  {
    or_bit = false;
    rlo_bit = xor_exprt{nesting_stack.back().rlo_bit, not_exprt{rlo_bit}};
  }
  nesting_stack.pop_back();
}

void statement_list_typecheckt::typecheck_statement_list_assign(
  const codet &op_code,
  symbolt &tia_element)
{
  const symbol_exprt &op{typecheck_instruction_with_non_const_operand(op_code)};
  const exprt lhs{typecheck_identifier(tia_element, op.get_identifier())};

  if(lhs.type() != rlo_bit.type())
  {
    error() << "Types of assign do not match" << eom;
    throw TYPECHECK_ERROR;
  }
  const code_assignt assignment{lhs, rlo_bit};
  tia_element.value.add_to_operands(assignment);
  fc_bit = false;
  or_bit = false;
  // Set RLO to assigned operand in order to prevent false results if a symbol
  // that's implicitly part of the RLO was changed by the assignment.
  rlo_bit = lhs;
}

void statement_list_typecheckt::typecheck_statement_list_set_rlo(
  const codet &op_code)
{
  typecheck_instruction_without_operand(op_code);
  fc_bit = false;
  or_bit = false;
  rlo_bit = true_exprt();
}

void statement_list_typecheckt::typecheck_statement_list_clr_rlo(
  const codet &op_code)
{
  typecheck_instruction_without_operand(op_code);
  fc_bit = false;
  or_bit = false;
  rlo_bit = false_exprt();
}

void statement_list_typecheckt::typecheck_statement_list_set(
  const codet &op_code,
  symbolt &tia_element)
{
  const symbol_exprt &op{typecheck_instruction_with_non_const_operand(op_code)};
  const irep_idt &identifier{op.get_identifier()};

  save_rlo_state(tia_element);

  const exprt lhs{typecheck_identifier(tia_element, identifier)};
  const code_assignt assignment{lhs, true_exprt()};
  const code_ifthenelset ifthen{rlo_bit, assignment};
  tia_element.value.add_to_operands(ifthen);
  fc_bit = false;
  or_bit = false;
}

void statement_list_typecheckt::typecheck_statement_list_reset(
  const codet &op_code,
  symbolt &tia_element)
{
  const symbol_exprt &op{typecheck_instruction_with_non_const_operand(op_code)};
  const irep_idt &identifier{op.get_identifier()};

  save_rlo_state(tia_element);

  const exprt lhs{typecheck_identifier(tia_element, identifier)};
  const code_assignt assignment{lhs, false_exprt()};
  const code_ifthenelset ifthen{rlo_bit, assignment};
  tia_element.value.add_to_operands(ifthen);
  fc_bit = false;
  or_bit = false;
}

void statement_list_typecheckt::typecheck_statement_list_call(
  const codet &op_code,
  symbolt &tia_element)
{
  const symbol_exprt &op{typecheck_instruction_with_non_const_operand(op_code)};
  const irep_idt &identifier{op.get_identifier()};
  if(symbol_table.has_symbol(identifier))
    typecheck_called_tia_element(op_code, tia_element);
  else if(identifier == CPROVER_ASSUME)
    typecheck_CPROVER_assume(op_code, tia_element);
  else if(identifier == CPROVER_ASSERT)
    typecheck_CPROVER_assert(op_code, tia_element);
  else
  {
    error() << "Called function could not be found" << eom;
    throw TYPECHECK_ERROR;
  }
  fc_bit = false;
  or_bit = false;
}

void statement_list_typecheckt::typecheck_statement_list_accu_int_arith(
  const codet &op_code)
{
  typecheck_binary_accumulator_instruction(op_code);
  const exprt &accu1{accumulator.back()};
  const exprt &accu2{accumulator.at(accumulator.size() - 2)};

  // Are both operands integers?
  const signedbv_typet *const accu_type1 =
    type_try_dynamic_cast<signedbv_typet>(accu1.type());
  const signedbv_typet *const accu_type2 =
    type_try_dynamic_cast<signedbv_typet>(accu2.type());
  if(
    !accu_type1 || !accu_type2 || accu_type1->get_width() != STL_INT_WIDTH ||
    accu_type2->get_width() != STL_INT_WIDTH)
  {
    error() << "Operands of integer addition are no integers" << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_statement_list_accu_dint_arith(
  const codet &op_code)
{
  typecheck_binary_accumulator_instruction(op_code);
  const exprt &accu1{accumulator.back()};
  const exprt &accu2{accumulator.at(accumulator.size() - 2)};

  // Are both operands double integers?
  const signedbv_typet *const accu_type1 =
    type_try_dynamic_cast<signedbv_typet>(accu1.type());
  const signedbv_typet *const accu_type2 =
    type_try_dynamic_cast<signedbv_typet>(accu2.type());
  if(
    !accu_type1 || !accu_type2 || accu_type1->get_width() != STL_DINT_WIDTH ||
    accu_type2->get_width() != STL_DINT_WIDTH)
  {
    error() << "Operands of double integer addition are no double integers"
            << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_statement_list_accu_real_arith(
  const codet &op_code)
{
  typecheck_binary_accumulator_instruction(op_code);
  const exprt &accu1{accumulator.back()};
  const exprt &accu2{accumulator.at(accumulator.size() - 2)};

  // Are both operands real types?
  if(!(can_cast_type<floatbv_typet>(accu1.type()) &&
       can_cast_type<floatbv_typet>(accu2.type())))
  {
    error() << "Operands of Real addition do not have the type Real" << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_accumulator_compare_instruction(
  const irep_idt &comparison)
{
  const exprt &accu1{accumulator.back()};
  const exprt &accu2{accumulator.at(accumulator.size() - 2)};
  // STL behaviour: ACCU2 is lhs, ACCU1 is rhs.
  const binary_relation_exprt operation{accu2, comparison, accu1};
  rlo_bit = operation;
}

const symbol_exprt &
statement_list_typecheckt::typecheck_instruction_with_non_const_operand(
  const codet &op_code)
{
  const symbol_exprt *const symbol =
    expr_try_dynamic_cast<symbol_exprt>(op_code.op0());

  if(symbol)
    return *symbol;

  error() << "Instruction is not followed by symbol" << eom;
  throw TYPECHECK_ERROR;
}

void statement_list_typecheckt::typecheck_instruction_without_operand(
  const codet &op_code)
{
  if(op_code.operands().size() > 0)
  {
    error() << "Instruction is followed by operand" << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_binary_accumulator_instruction(
  const codet &op_code)
{
  typecheck_instruction_without_operand(op_code);
  if(accumulator.size() < 2)
  {
    error() << "Not enough operands in the accumulator" << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_nested_boolean_instruction(
  const codet &op_code,
  const exprt &rlo_value)
{
  typecheck_instruction_without_operand(op_code);
  // If inside of a bit string use the value of the rlo. If this is the first
  // expression of a bit string, load the value of the nested operation by
  // implicitly setting the rlo to the specified value.
  if(!fc_bit)
    rlo_bit = rlo_value;
  const nesting_stack_entryt stack_entry{rlo_bit, or_bit, op_code};
  nesting_stack.push_back(stack_entry);
  fc_bit = false;
  or_bit = false;
}

exprt statement_list_typecheckt::typecheck_simple_boolean_instruction_operand(
  const codet &op_code,
  const symbolt &tia_element,
  bool negate)
{
  const symbol_exprt &sym{
    typecheck_instruction_with_non_const_operand(op_code)};
  const exprt op{typecheck_identifier(tia_element, sym.get_identifier())};
  const not_exprt not_op{op};
  return negate ? not_op : op;
}

exprt statement_list_typecheckt::typecheck_identifier(
  const symbolt &tia_element,
  const irep_idt &identifier)
{
  const code_typet &element_type{to_code_type(tia_element.type)};

  // Check for temporary variables.
  if(symbol_table.has_symbol(
       id2string(tia_element.name) + "::" + id2string(identifier)))
  {
    const symbolt &sym{symbol_table.lookup_ref(
      id2string(tia_element.name) + "::" + id2string(identifier))};
    return sym.symbol_expr();
  }

  // Check for global tags.
  if(symbol_table.has_symbol(identifier))
    return symbol_table.lookup_ref(identifier).symbol_expr();

  if(
    element_type.get(ID_statement_list_type) ==
    ID_statement_list_function_block)
  {
    // Check for variables inside of the function block interface.
    const symbolt &data_block{symbol_table.get_writeable_ref(
      id2string(tia_element.name) + "::" + DATA_BLOCK_PARAMETER_NAME)};
    const symbol_exprt db_expr = data_block.symbol_expr();
    const struct_typet *const db_type =
      type_try_dynamic_cast<struct_typet>(db_expr.type().subtype());
    if(!db_type)
      UNREACHABLE;
    for(const struct_union_typet::componentt &member : db_type->components())
    {
      if(member.get_name() == identifier)
      {
        const dereference_exprt deref_db{db_expr};
        const member_exprt val{deref_db, member.get_name(), member.type()};
        return val;
      }
    }
  }
  else if(
    element_type.get(ID_statement_list_type) == ID_statement_list_function)
  {
    // Check for variables inside of the function interface.
    for(const auto &member : element_type.parameters())
    {
      if(member.get_base_name() == identifier)
      {
        const symbolt &par{
          symbol_table.get_writeable_ref(member.get_identifier())};
        return par.symbol_expr();
      }
    }
  }
  else
    UNREACHABLE; // Variable declarations should only be checked for FCs or FBs

  error() << "Identifier could not be found in project" << eom;
  throw TYPECHECK_ERROR;
}

void statement_list_typecheckt::typecheck_CPROVER_assert(
  const codet &op_code,
  symbolt &tia_element)
{
  const equal_exprt *const assignment =
    expr_try_dynamic_cast<equal_exprt>(op_code.op1());
  if(assignment)
  {
    const code_assertt assertion{
      typecheck_function_call_argument_rhs(tia_element, assignment->rhs())};
    tia_element.value.add_to_operands(assertion);
  }
  else
  {
    error() << "No assignment found for assertion" << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_CPROVER_assume(
  const codet &op_code,
  symbolt &tia_element)
{
  const equal_exprt *const assignment =
    expr_try_dynamic_cast<equal_exprt>(op_code.op1());
  if(assignment)
  {
    const code_assumet assumption{
      typecheck_function_call_argument_rhs(tia_element, assignment->rhs())};
    tia_element.value.add_to_operands(assumption);
  }
  else
  {
    error() << "No assignment found for assumption" << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_called_tia_element(
  const codet &op_code,
  symbolt &tia_element)
{
  const symbol_exprt &call_operand{to_symbol_expr(op_code.op0())};
  const symbolt &called_function{
    symbol_table.lookup_ref(call_operand.get_identifier())};
  const code_typet &called_type{to_code_type(called_function.type)};
  // Is it a STL function or STL function block?
  if(
    called_type.get(ID_statement_list_type) == ID_statement_list_function_block)
    typecheck_called_function_block(op_code, tia_element);
  else if(called_type.get(ID_statement_list_type) == ID_statement_list_function)
    typecheck_called_function(op_code, tia_element);
  else
  {
    error() << "Tried to call element that is no function or function block"
            << eom;
    throw TYPECHECK_ERROR;
  }
}

void statement_list_typecheckt::typecheck_called_function(
  const codet &op_code,
  symbolt &tia_element)
{
  const symbol_exprt call_operand{to_symbol_expr(op_code.op0())};
  const symbolt &called_function_sym{
    symbol_table.lookup_ref(call_operand.get_identifier())};
  const symbol_exprt called_function_expr{called_function_sym.symbol_expr()};
  const code_typet &called_type{to_code_type(called_function_sym.type)};

  // Check if function name is followed by data block.
  if(!can_cast_expr<equal_exprt>(op_code.op1()))
  {
    error() << "Function calls should not address instance data blocks" << eom;
    throw TYPECHECK_ERROR;
  }

  // Check if function interface matches the call and fill argument list.
  const code_typet::parameterst &params{called_type.parameters()};
  code_function_callt::argumentst args;
  std::vector<equal_exprt> assignments;
  for(const auto &expr : op_code.operands())
  {
    if(can_cast_expr<equal_exprt>(expr))
      assignments.push_back(to_equal_expr(expr));
  }

  for(const code_typet::parametert &param : params)
    args.emplace_back(
      typecheck_function_call_arguments(assignments, param, tia_element));

  // Check the return value if present.
  if(called_type.return_type().is_nil())
    tia_element.value.add_to_operands(
      code_function_callt{called_function_expr, args});
  else
  {
    const exprt lhs{typecheck_return_value_assignment(
      assignments, called_type.return_type(), tia_element)};
    tia_element.value.add_to_operands(
      code_function_callt{lhs, called_function_expr, args});
  }
}

void statement_list_typecheckt::typecheck_called_function_block(
  const codet &op_code,
  symbolt &tia_element)
{
  // TODO: Implement support for function block calls.
  // Needs code statements which assign the parameters to the instance data
  // block, call the function and write the result back to the parameters
  // afterwards.
  error() << "Calls to function blocks are not supported yet" << eom;
  throw TYPECHECK_ERROR;
}

exprt statement_list_typecheckt::typecheck_function_call_arguments(
  const std::vector<equal_exprt> &assignments,
  const code_typet::parametert &param,
  const symbolt &tia_element)
{
  const irep_idt &param_name = param.get_base_name();
  const typet &param_type = param.type();
  for(const equal_exprt &assignment : assignments)
  {
    const symbol_exprt &lhs{to_symbol_expr(assignment.lhs())};
    if(param_name == lhs.get_identifier())
    {
      exprt assigned_variable{
        typecheck_function_call_argument_rhs(tia_element, assignment.rhs())};

      if(param_type == assigned_variable.type())
        return assigned_variable;
      else
      {
        error() << "Types of parameter assignment do not match: "
                << param.type().id() << " != " << assigned_variable.type().id()
                << eom;
        throw TYPECHECK_ERROR;
      }
    }
  }
  error() << "No assignment found for function parameter "
          << param.get_identifier() << eom;
  throw TYPECHECK_ERROR;
}

exprt statement_list_typecheckt::typecheck_function_call_argument_rhs(
  const symbolt &tia_element,
  const exprt &rhs)
{
  exprt assigned_operand;
  const symbol_exprt *const symbol_rhs =
    expr_try_dynamic_cast<symbol_exprt>(rhs);
  if(symbol_rhs)
    assigned_operand =
      typecheck_identifier(tia_element, symbol_rhs->get_identifier());
  else // constant_exprt.
    assigned_operand = rhs;
  return assigned_operand;
}

exprt statement_list_typecheckt::typecheck_return_value_assignment(
  const std::vector<equal_exprt> &assignments,
  const typet &return_type,
  const symbolt &tia_element)
{
  for(const equal_exprt &assignment : assignments)
  {
    const symbol_exprt &lhs{to_symbol_expr(assignment.lhs())};
    if(ID_statement_list_return_value_id == lhs.get_identifier())
    {
      const symbol_exprt &rhs{to_symbol_expr(assignment.rhs())};
      const exprt assigned_variable{
        typecheck_identifier(tia_element, rhs.get_identifier())};
      if(return_type == assigned_variable.type())
        return assigned_variable;
      else
      {
        error() << "Types of return value assignment do not match: "
                << return_type.id() << " != " << assigned_variable.type().id()
                << eom;
        throw TYPECHECK_ERROR;
      }
    }
  }
  error() << "No assignment found for function return value" << eom;
  throw TYPECHECK_ERROR;
}

void statement_list_typecheckt::add_to_or_rlo_wrapper(const exprt &op)
{
  or_exprt or_wrapper{to_or_expr(rlo_bit)};

  if(can_cast_expr<constant_exprt>(or_wrapper.op1()))
    or_wrapper.op1();
  else if(can_cast_expr<and_exprt>(or_wrapper.op1()))
  {
    and_exprt &and_op{to_and_expr(or_wrapper.op1())};
    and_op.add_to_operands(op);
    or_wrapper.op1() = and_op;
  }
  else
  {
    and_exprt and_op{or_wrapper.op1(), op};
    or_wrapper.op1() = and_op;
  }
  rlo_bit = or_wrapper;
}

void statement_list_typecheckt::initialize_bit_expression(const exprt &op)
{
  fc_bit = true;
  or_bit = false;
  rlo_bit = op;
}

void statement_list_typecheckt::save_rlo_state(symbolt &tia_element)
{
  symbol_exprt temp_rlo{
    symbol_table.lookup_ref(CPROVER_TEMP_RLO).symbol_expr()};
  const code_assignt rlo_assignment{temp_rlo, rlo_bit};
  tia_element.value.add_to_operands(rlo_assignment);
  rlo_bit = std::move(temp_rlo);
}
