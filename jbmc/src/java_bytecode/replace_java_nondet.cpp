/*******************************************************************\

Module: Replace Java Nondet expressions

Author: Reuben Thomas, reuben.thomas@diffblue.com

\*******************************************************************/

/// \file
/// Replace Java Nondet expressions

#include "replace_java_nondet.h"

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include <util/std_code.h>

#include <algorithm>
#include <regex>

/// Holds information about any discovered nondet methods, with extreme type-
/// safety.
class nondet_instruction_infot final
{
public:
  enum class is_nondett : bool
  {
    FALSE,
    TRUE
  };
  enum class is_nullablet : bool
  {
    FALSE,
    TRUE
  };

  nondet_instruction_infot()
    : is_nondet(is_nondett::FALSE), is_nullable(is_nullablet::FALSE)
  {
  }

  explicit nondet_instruction_infot(is_nullablet is_nullable)
    : is_nondet(is_nondett::TRUE), is_nullable(is_nullable)
  {
  }

  is_nondett get_instruction_type() const
  {
    return is_nondet;
  }
  is_nullablet get_nullable_type() const
  {
    return is_nullable;
  }

private:
  is_nondett is_nondet;
  is_nullablet is_nullable;
};

/// Checks whether the function call is one of our nondet library functions.
/// \param function_call: The function call declaration to check.
/// \return A structure detailing whether the function call appears to be one of
///   our nondet library methods, and if so, whether or not it allows null
///   results.
static nondet_instruction_infot
is_nondet_returning_object(const code_function_callt &function_call)
{
  const auto &function_symbol = to_symbol_expr(function_call.function());
  const auto function_name = id2string(function_symbol.get_identifier());
  const std::regex reg(
    R"(.*org\.cprover\.CProver\.nondet)"
    R"((?:Boolean|Byte|Char|Short|Int|Long|Float|Double|With(out)?Null.*))");
  std::smatch match_results;
  if(!std::regex_match(function_name, match_results, reg))
  {
    return nondet_instruction_infot();
  }

  return nondet_instruction_infot(
    nondet_instruction_infot::is_nullablet(!match_results[1].matched));
}

/// Check whether the instruction is a function call which matches one of the
/// recognised nondet library methods, and return some information about it.
/// \param instr: A goto-program instruction to check.
/// \return A structure detailing the properties of the nondet method.
static nondet_instruction_infot
get_nondet_instruction_info(const goto_programt::const_targett &instr)
{
  if(!(instr->is_function_call() && instr->code().id() == ID_code))
  {
    return nondet_instruction_infot();
  }
  const auto &code = instr->code();
  INVARIANT(
    code.get_statement() == ID_function_call,
    "function_call should have ID_function_call");
  const auto &function_call = to_code_function_call(code);
  return is_nondet_returning_object(function_call);
}

/// Return whether the expression is a symbol with the specified identifier.
/// \param expr: The expression which may be a symbol.
/// \param identifier: Some identifier.
/// \return True if the expression is a symbol with the specified identifier.
static bool is_symbol_with_id(const exprt &expr, const irep_idt &identifier)
{
  return expr.id() == ID_symbol &&
         to_symbol_expr(expr).get_identifier() == identifier;
}

/// Return whether the expression is a typecast with the specified identifier.
/// \param expr: The expression which may be a typecast.
/// \param identifier: Some identifier.
/// \return True if the expression is a typecast with one operand, and the
///   typecast's identifier matches the specified identifier.
static bool is_typecast_with_id(const exprt &expr, const irep_idt &identifier)
{
  if(!(expr.id() == ID_typecast && expr.operands().size() == 1))
  {
    return false;
  }
  const auto &typecast = to_typecast_expr(expr);
  if(!(typecast.op().id() == ID_symbol && !typecast.op().has_operands()))
  {
    return false;
  }
  const auto &op_symbol = to_symbol_expr(typecast.op());
  // Return whether the typecast has the expected operand
  return op_symbol.get_identifier() == identifier;
}

/// Return whether the instruction is an assignment, and the rhs is a symbol or
/// typecast expression with the specified identifier.
/// \param instr: A goto program instruction.
/// \param identifier: Some identifier.
/// \return True if the expression is a typecast with one operand, and the
///   typecast's identifier matches the specified identifier.
static bool is_assignment_from(
  const goto_programt::instructiont &instr,
  const irep_idt &identifier)
{
  // If not an assignment, return false
  if(!instr.is_assign())
  {
    return false;
  }
  const auto &rhs = instr.assign_rhs();
  return is_symbol_with_id(rhs, identifier) ||
         is_typecast_with_id(rhs, identifier);
}

/// Return whether the instruction is a return, and the rhs is a symbol or
/// typecast expression with the specified identifier.
/// \param instr: A goto program instruction.
/// \param identifier: Some identifier.
/// \return True if the expression is a typecast with one operand, and the
///   typecast's identifier matches the specified identifier.
static bool is_return_with_variable(
  const goto_programt::instructiont &instr,
  const irep_idt &identifier)
{
  if(!instr.is_set_return_value())
  {
    return false;
  }
  const auto &rhs = instr.return_value();
  return is_symbol_with_id(rhs, identifier) ||
         is_typecast_with_id(rhs, identifier);
}

/// Given an iterator into a list of instructions, modify the list to replace
/// 'nondet' library functions with CBMC-native nondet expressions, and return
/// an iterator to the next instruction to check. It's important to note that
/// this method also deals with the fact that in the GOTO program it assigns
/// function return values to temporary variables, performs validation and then
/// assigns the value into the actual variable.
///
/// Example:
///
///   return_tmp0=org.cprover.CProver.nondetWithoutNull:()Ljava/lang/Object;();
///   ... Various validations of type and value here.
///   obj = (<type-of-obj>)return_tmp0;
///
/// We're going to replace all of these lines with
///   obj = NONDET(<type-of-obj>)
///
/// In the situation of a direct return, the end result should be:
///   return NONDET(<type-of-obj>)
/// \param goto_program: The goto program to modify.
/// \param target: A single step of the goto program which may be erased and
///   replaced.
/// \return The next instruction to process, probably with this function.
static goto_programt::targett check_and_replace_target(
  goto_programt &goto_program,
  const goto_programt::targett &target)
{
  // Check whether this is a nondet library method, and return if not
  const auto instr_info = get_nondet_instruction_info(target);
  const auto next_instr = std::next(target);
  if(
    instr_info.get_instruction_type() ==
    nondet_instruction_infot::is_nondett::FALSE)
  {
    return next_instr;
  }

  // If we haven't removed returns yet, our function call will have a variable
  // on its left hand side.
  const bool remove_returns_not_run = target->call_lhs().is_not_nil();

  irep_idt return_identifier;
  if(remove_returns_not_run)
  {
    return_identifier = to_symbol_expr(target->call_lhs()).get_identifier();
  }
  else
  {
    // If not, we need to look at the next line instead.
    DATA_INVARIANT(
      next_instr->is_assign(),
      "the code_function_callt for a nondet-returning library function should "
      "either have a variable for the return value in its lhs() or the next "
      "instruction should be an assignment of the return value to a temporary "
      "variable");
    const exprt &return_value_assignment = next_instr->assign_lhs();

    // If the assignment is null, return.
    if(
      !(return_value_assignment.id() == ID_symbol &&
        !return_value_assignment.has_operands()))
    {
      return next_instr;
    }

    // Otherwise it's the temporary variable.
    return_identifier =
      to_symbol_expr(return_value_assignment).get_identifier();
  }

  // Look for the assignment of the temporary return variable into our target
  // variable.
  const auto end = goto_program.instructions.end();
  auto target_instruction = std::find_if(
    next_instr,
    end,
    [&return_identifier](const goto_programt::instructiont &instr) {
      return is_assignment_from(instr, return_identifier);
    });

  // If we can't find an assign, it might be a direct return.
  if(target_instruction == end)
  {
    target_instruction = std::find_if(
      next_instr,
      end,
      [&return_identifier](const goto_programt::instructiont &instr) {
        return is_return_with_variable(instr, return_identifier);
      });
  }

  INVARIANT(
    target_instruction != end,
    "failed to find return of the temporary return variable or assignment of "
    "the temporary return variable into a target variable");

  std::for_each(
    target, target_instruction, [](goto_programt::instructiont &instr) {
      instr.turn_into_skip();
    });

  if(target_instruction->is_set_return_value())
  {
    const auto &nondet_var = target_instruction->return_value();

    side_effect_expr_nondett inserted_expr(
      nondet_var.type(), target_instruction->source_location());
    inserted_expr.set_nullable(
      instr_info.get_nullable_type() ==
      nondet_instruction_infot::is_nullablet::TRUE);
    target_instruction->code_nonconst() = code_returnt(inserted_expr);
    target_instruction->code_nonconst().add_source_location() =
      target_instruction->source_location();
  }
  else if(target_instruction->is_assign())
  {
    // Assume that the LHS of *this* assignment is the actual nondet variable
    const auto &nondet_var = target_instruction->assign_lhs();

    side_effect_expr_nondett inserted_expr(
      nondet_var.type(), target_instruction->source_location());
    inserted_expr.set_nullable(
      instr_info.get_nullable_type() ==
      nondet_instruction_infot::is_nullablet::TRUE);
    target_instruction->code_nonconst() =
      code_assignt(nondet_var, inserted_expr);
    target_instruction->code_nonconst().add_source_location() =
      target_instruction->source_location();
  }

  goto_program.update();

  return std::next(target_instruction);
}

/// Checks each instruction in the goto program to see whether it is a method
/// returning nondet.  If it is, replaces the function call with an irep
/// representing a nondet side effect with an appropriate type.
/// \param goto_program: The goto program to modify.
static void replace_java_nondet(goto_programt &goto_program)
{
  for(auto instruction_iterator = goto_program.instructions.begin(),
           end = goto_program.instructions.end();
      instruction_iterator != end;)
  {
    instruction_iterator =
      check_and_replace_target(goto_program, instruction_iterator);
  }
}

/// Replace calls to nondet library functions with an internal nondet
/// representation in a single function.
/// \param function: The goto program to modify.
void replace_java_nondet(goto_model_functiont &function)
{
  goto_programt &program = function.get_goto_function().body;
  replace_java_nondet(program);

  remove_skip(program);
}

void replace_java_nondet(goto_functionst &goto_functions)
{
  for(auto &goto_program : goto_functions.function_map)
  {
    replace_java_nondet(goto_program.second.body);
  }

  remove_skip(goto_functions);
}

/// Replace calls to nondet library functions with an internal nondet
/// representation.
/// \param goto_model: The goto program to modify.
void replace_java_nondet(goto_modelt &goto_model)
{
  replace_java_nondet(goto_model.goto_functions);
}
