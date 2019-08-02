/*******************************************************************\

Module: Insert assert(false) at end of entry function

Author: Nathan Chong, Kareem Khazem

\*******************************************************************/

/// \file
/// Insert final assert false into a function

#include "insert_final_assert_false.h"

#include <goto-programs/goto_model.h>
#include <util/irep.h>

#include <iterator>
#include <list>

insert_final_assert_falset::insert_final_assert_falset(
  message_handlert &_message_handler)
  : log(_message_handler)
{
}

bool insert_final_assert_falset::
operator()(goto_modelt &goto_model, const std::string &function_to_instrument)
{
  const irep_idt entry(function_to_instrument);
  auto it = goto_model.goto_functions.function_map.find(entry);
  if(it == goto_model.goto_functions.function_map.end())
  {
    log.error() << "insert-final-assert-false: could not find function "
                << "'" << function_to_instrument << "'" << messaget::eom;
    return true;
  }
  goto_programt &entry_function = (it->second).body;
  goto_programt::instructionst &instructions = entry_function.instructions;
  auto instr_it = instructions.end();
  auto last_instruction = std::prev(instr_it);
  DATA_INVARIANT(
    last_instruction->is_end_function(),
    "last instruction in function should be END_FUNCTION");
  source_locationt assert_location = last_instruction->source_location;
  assert_location.set_property_class(ID_assertion);
  assert_location.set_comment("insert-final-assert-false (should fail) ");
  goto_programt::instructiont false_assert =
    goto_programt::make_assertion(false_exprt(), assert_location);
  entry_function.insert_before_swap(last_instruction, false_assert);
  return false;
}

bool insert_final_assert_false(
  goto_modelt &goto_model,
  const std::string &function_to_instrument,
  message_handlert &message_handler)
{
  insert_final_assert_falset ifaf(message_handler);
  return ifaf(goto_model, function_to_instrument);
}
