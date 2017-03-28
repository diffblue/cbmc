/*******************************************************************\

Module: Remove Java Nondet expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

/// \file
/// Replace Java Nondet expressions

#include "goto-programs/replace_java_nondet.h"
#include "goto-programs/goto_convert.h"
#include "goto-programs/goto_model.h"

#include "java_bytecode/java_object_factory.h"

#include "util/irep_ids.h"

#include <algorithm>
#include <regex>

/// Holds information about any discovered nondet methods, with extreme type-
/// safety.
class nondet_instruction_infot final
{
  bool is_nondet_instruction;
  bool is_never_null;
};

/// Checks whether the function call is one of our nondet library functions.
/// \param function_call: The function call declaration to check.
/// \return A structure detailing whether the function call appears to be one of
///   our nondet library methods, and if so, whether or not it allows null
///   results.
static nondet_instruction_infot is_nondet_returning_object(
  const code_function_callt &function_call)
{
  const auto &function_symbol=to_symbol_expr(function_call.function());
  const auto function_name=id2string(function_symbol.get_identifier());
  std::smatch match_results;
  if(!std::regex_match(
       function_name,
       match_results,
       std::regex(".*org\\.cprover\\.CProver\\.nondetWith(out)?Null.*")))
  {
    return {false, false};
  }

  return {true, match_results[1].matched};
}

/// Check whether the instruction is a function call which matches one of the
/// recognised nondet library methods, and return some information about it.
/// \param instr: A goto-program instruction to check.
/// \return A structure detailing the properties of the nondet method.
static nondet_instruction_infot get_nondet_instruction_info(
  const goto_programt::targett &instr)
{
  if(!(instr->is_function_call() && instr->code.id()==ID_code))
  {
    return {false, false};
  }
  const auto &code=to_code(instr->code);
  if(code.get_statement()!=ID_function_call)
  {
    return {false, false};
  }
  const auto &function_call=to_code_function_call(code);
  return is_nondet_returning_object(function_call);
}

/// Return whether the expression is a symbol with the specified identifier.
/// \param expr: The expression which may be a symbol.
/// \param identifier: Some identifier.
/// \return True if the expression is a symbol with the specified identifier.
static bool is_symbol_with_id(const exprt& expr, const irep_idt& identifier)
{
  return expr.id()==ID_symbol &&
         to_symbol_expr(expr).get_identifier()==identifier;
}

/// Return whether the expression is a typecast with the specified identifier.
/// \param expr: The expression which may be a typecast.
/// \param identifier: Some identifier.
/// \return True if the expression is a typecast with one operand, and the
///   typecast's identifier matches the specified identifier.
static bool is_typecast_with_id(const exprt& expr, const irep_idt& identifier)
{
  if(!(expr.id()==ID_typecast && expr.operands().size()==1))
  {
    return false;
  }
  const auto &typecast=to_typecast_expr(expr);
  if(!(typecast.op().id()==ID_symbol && !typecast.op().has_operands()))
  {
    return false;
  }
  const auto &op_symbol=to_symbol_expr(typecast.op());
  // Return whether the typecast has the expected operand
  return op_symbol.get_identifier()==identifier;
}

/// Return whether the instruction is an assignment, and the rhs is a symbol or
/// typecast expression with the specified identifier.
/// \param instr: A goto program instruction.
/// \param identifier: Some identifier.
/// \return True if the expression is a typecast with one operand, and the
///   typecast's identifier matches the specified identifier.
static bool is_assignment_from(
  const goto_programt::instructiont &instr,
  const dstringt &identifier)
{
  // If not an assignment, return false
  if(!instr.is_assign())
  {
    return false;
  }
  const auto &rhs=to_code_assign(instr.code).rhs();
  return is_symbol_with_id(rhs, identifier) ||
         is_typecast_with_id(rhs, identifier);
}

/// Given an iterator into a list of instructions, modify the list to replace
/// 'nondet' library functions with CBMC-native nondet expressions, and return
/// an iterator to the next instruction to check.
/// \param goto_program: The goto program to modify.
/// \param target: A single step of the goto program which may be erased and
///   replaced.
/// \return The next instruction to process, probably with this function.
static goto_programt::targett check_and_replace_target(
  goto_programt &goto_program,
  const goto_programt::targett &target)
{
  // Check whether this is our nondet library method, and return if not
  const auto instr_info=get_nondet_instruction_info(instr);
  const auto next_instr=std::next(instr);
  if(!instr_info.is_nondet_instruction)
  {
    return next_instr;
  }

  // Look at the next instruction, ensure that it is an assignment
  assert(next_instr->is_assign());
  // Get the name of the LHS of the assignment
  const auto &next_instr_assign_lhs=to_code_assign(next_instr->code).lhs();
  if(!(next_instr_assign_lhs.id()==ID_symbol &&
       !next_instr_assign_lhs.has_operands()))
  {
    return next_instr;
  }
  const auto return_identifier=
    to_symbol_expr(next_instr_assign_lhs).get_identifier();

  auto &instructions=prog.instructions;
  const auto end=std::end(instructions);

  // Look for an instruction where this name is on the RHS of an assignment
  const auto matching_assignment=std::find_if(
    next_instr,
    end,
    [&return_identifier](const goto_programt::instructiont &instr)
    {
      return is_assignment_from(instr, return_identifier);
    });

  assert(matching_assignment!=end);

  // Assume that the LHS of *this* assignment is the actual nondet variable
  const auto &code_assign=to_code_assign(matching_assignment->code);
  const auto nondet_var=code_assign.lhs();
  const auto source_loc=instr->source_location;

  // Erase from the nondet function call to the assignment
  const auto after_matching_assignment=std::next(matching_assignment);
  assert(after_matching_assignment!=end);
  const auto after_erased=
    instructions.erase(instr, after_matching_assignment);

  // Generate nondet init code
  code_blockt init_code;
  gen_nondet_init(
    nondet_var,
    init_code,
    symbol_table,
    source_loc,
    false,
    true,
    instr_info.is_never_null,
    message_handler,
    max_nondet_array_length);

  // Convert this code into goto instructions
  goto_programt new_instructions;
  goto_convert(init_code, symbol_table, new_instructions, message_handler);

  // Insert the new instructions into the instruction list
  prog.destructive_insert(after_erased, new_instructions);
  prog.update();

  return after_erased;
}

/// Checks each instruction in the goto program to see whether it is a method
/// returning nondet.  If it is, replaces the function call with an irep
/// representing a nondet side effect with an appropriate type.
/// \param goto_program: The goto program to modify.
static void replace_java_nondet(goto_programt &goto_program)
{
  // Check each instruction.
  // `process_target` may modify the list in place, and returns the next
  // iterator to look at.
  for(auto instruction_iterator=std::begin(goto_program.instructions),
        end=std::end(goto_program.instructions);
      instruction_iterator!=end;
      instruction_iterator=process_target(
        message_handler,
        symbol_table,
        max_nondet_array_length,
        goto_program,
        instruction_iterator))
  {
    // Loop body deliberately empty.
  }
}

void remove_java_nondet(
  message_handlert &message_handler,
  symbol_tablet &symbol_table,
  const size_t max_nondet_array_length,
  goto_functionst &goto_functions)
{
  for(auto &f : goto_functions.function_map)
  {
    remove_java_nondet(
      message_handler,
      symbol_table,
      max_nondet_array_length,
      f.second.body);
  }
  goto_functions.compute_location_numbers();
}
