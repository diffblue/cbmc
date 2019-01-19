/*******************************************************************\

Module: Convert side_effect_expr_nondett expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

/// \file
/// Convert side_effect_expr_nondett expressions

#include "convert_java_nondet.h"

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include <util/fresh_symbol.h>
#include <util/irep_ids.h>

#include <memory>

#include "java_object_factory.h" // gen_nondet_init

/// Returns true if `expr` is a nondet pointer that isn't a function pointer or
/// a void* pointer as these can be meaningfully non-det initialized.
static bool is_nondet_pointer(exprt expr)
{
  // If the expression type doesn't have a subtype then I guess it's primitive
  // and we do not want to convert it. If the type is a ptr-to-void or a
  // function pointer then we also do not want to convert it.
  const typet &type = expr.type();
  const bool non_void_non_function_pointer = type.id() == ID_pointer &&
                                             type.subtype().id() != ID_empty &&
                                             type.subtype().id() != ID_code;
  return can_cast_expr<side_effect_expr_nondett>(expr) &&
         non_void_non_function_pointer;
}

/// Populate `instructions` with goto instructions to nondet init
/// `aux_symbol_expr`
static goto_programt get_gen_nondet_init_instructions(
  const symbol_exprt &aux_symbol_expr,
  const source_locationt &source_loc,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const java_object_factory_parameterst &object_factory_parameters,
  const irep_idt &mode)
{
  code_blockt gen_nondet_init_code;
  const bool skip_classid = true;
  gen_nondet_init(
    aux_symbol_expr,
    gen_nondet_init_code,
    symbol_table,
    source_loc,
    skip_classid,
    lifetimet::DYNAMIC,
    object_factory_parameters,
    update_in_placet::NO_UPDATE_IN_PLACE);

  goto_programt instructions;
  goto_convert(
    gen_nondet_init_code, symbol_table, instructions, message_handler, mode);
  return instructions;
}

/// Checks an instruction to see whether it contains an assignment from
/// side_effect_expr_nondet.  If so, replaces the instruction with a range of
/// instructions to properly nondet-initialize the lhs.
/// \param function_identifier: Name of the function containing \p target.
/// \param goto_program: The goto program to modify.
/// \param target: One of the steps in that goto program.
/// \param symbol_table: The global symbol table.
/// \param message_handler: Handles logging.
/// \param object_factory_parameters: Parameters for the generation of nondet
///   objects.
/// \param mode: Language mode
/// \return The next instruction to process with this function and a boolean
///   indicating whether any changes were made to the goto program.
static std::pair<goto_programt::targett, bool> insert_nondet_init_code(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  const goto_programt::targett &target,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  java_object_factory_parameterst object_factory_parameters,
  const irep_idt &mode)
{
  const auto next_instr = std::next(target);

  // We only expect to find nondets in the rhs of an assignments, and in return
  // statements if remove_returns has not been run, but we do a more general
  // check on all operands in case this changes
  for(exprt &op : target->code.operands())
  {
    if(!is_nondet_pointer(op))
    {
      continue;
    }

    const auto &nondet_expr = to_side_effect_expr_nondet(op);

    if(!nondet_expr.get_nullable())
      object_factory_parameters.min_null_tree_depth = 1;

    const source_locationt &source_loc = target->source_location;

    // Currently the code looks like this
    //   target: instruction containing op
    // When we are done it will look like this
    //   target : declare aux_symbol
    //      .     <gen_nondet_init_instructions - many lines>
    //      .     <gen_nondet_init_instructions - many lines>
    //      .     <gen_nondet_init_instructions - many lines>
    //   target2: instruction containing op, with op replaced by aux_symbol
    //            dead aux_symbol

    symbolt &aux_symbol = get_fresh_aux_symbol(
      op.type(),
      id2string(function_identifier),
      "nondet_tmp",
      source_loc,
      ID_java,
      symbol_table);

    const symbol_exprt aux_symbol_expr = aux_symbol.symbol_expr();
    op = aux_symbol_expr;

    // Insert an instruction declaring `aux_symbol` before `target`, being
    // careful to preserve jumps to `target`
    goto_programt::instructiont decl_aux_symbol;
    decl_aux_symbol.make_decl(code_declt(aux_symbol_expr));
    decl_aux_symbol.source_location = source_loc;
    goto_program.insert_before_swap(target, decl_aux_symbol);

    // Keep track of the new location of the instruction containing op.
    const goto_programt::targett target2 = std::next(target);

    goto_programt gen_nondet_init_instructions =
      get_gen_nondet_init_instructions(
        aux_symbol_expr,
        source_loc,
        symbol_table,
        message_handler,
        object_factory_parameters,
        mode);
    goto_program.destructive_insert(target2, gen_nondet_init_instructions);

    goto_programt::targett dead_aux_symbol = goto_program.insert_after(target2);
    dead_aux_symbol->make_dead();
    dead_aux_symbol->code = code_deadt(aux_symbol_expr);
    dead_aux_symbol->source_location = source_loc;

    // In theory target could have more than one operand which should be
    // replaced by convert_nondet, so we return target2 so that it
    // will be checked again
    return std::make_pair(target2, true);
  }

  return std::make_pair(next_instr, false);
}

/// For each instruction in the goto program, checks if it is an assignment from
/// nondet and replaces it with the appropriate composite initialization code if
/// so.
/// \param function_identifier: Name of the function \p goto_program.
/// \param goto_program: The goto program to modify.
/// \param symbol_table: The global symbol table.
/// \param message_handler: Handles logging.
/// \param object_factory_parameters: Parameters for the generation of nondet
///   objects.
/// \param mode: Language mode
void convert_nondet(
  const irep_idt &function_identifier,
  goto_programt &goto_program,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const java_object_factory_parameterst &object_factory_parameters,
  const irep_idt &mode)
{
  bool changed = false;
  auto instruction_iterator = goto_program.instructions.begin();

  while(instruction_iterator != goto_program.instructions.end())
  {
    auto ret = insert_nondet_init_code(
      function_identifier,
      goto_program,
      instruction_iterator,
      symbol_table,
      message_handler,
      object_factory_parameters,
      mode);
    instruction_iterator = ret.first;
    changed |= ret.second;
  }

  if(changed)
  {
    goto_program.update();
  }
}

void convert_nondet(
  goto_model_functiont &function,
  message_handlert &message_handler,
  const java_object_factory_parameterst &object_factory_parameters,
  const irep_idt &mode)
{
  java_object_factory_parameterst parameters = object_factory_parameters;
  parameters.function_id = function.get_function_id();
  convert_nondet(
    function.get_function_id(),
    function.get_goto_function().body,
    function.get_symbol_table(),
    message_handler,
    parameters,
    mode);

  function.compute_location_numbers();
}

void convert_nondet(
  goto_functionst &goto_functions,
  symbol_table_baset &symbol_table,
  message_handlert &message_handler,
  const java_object_factory_parameterst &object_factory_parameters)
{
  const namespacet ns(symbol_table);

  for(auto &f_it : goto_functions.function_map)
  {
    const symbolt &symbol=ns.lookup(f_it.first);

    if(symbol.mode==ID_java)
    {
      java_object_factory_parameterst parameters = object_factory_parameters;
      parameters.function_id = f_it.first;
      convert_nondet(
        f_it.first,
        f_it.second.body,
        symbol_table,
        message_handler,
        object_factory_parameters,
        symbol.mode);
    }
  }

  goto_functions.compute_location_numbers();

  remove_skip(goto_functions);
}

void convert_nondet(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  const java_object_factory_parameterst &object_factory_parameters)
{
  convert_nondet(
    goto_model.goto_functions,
    goto_model.symbol_table,
    message_handler,
    object_factory_parameters);
}
