/*******************************************************************\

Module: A GOTO Function

Author: Daniel Kroening

Date: May 2018

\*******************************************************************/

/// \file
/// Goto Function

#include "goto_function.h"

#include <util/format_expr.h>
#include <util/json_irep.h>
#include <util/xml_irep.h>

/// Return in \p dest the identifiers of the local variables declared in the \p
/// goto_function and the identifiers of the paramters of the \p goto_function.
void get_local_identifiers(
  const goto_functiont &goto_function,
  std::set<irep_idt> &dest)
{
  goto_function.body.get_decl_identifiers(dest);

  // add parameters
  for(const auto &identifier : goto_function.parameter_identifiers)
  {
    if(!identifier.empty())
      dest.insert(identifier);
  }
}

/// Check that the goto function is well-formed
///
/// The validation mode indicates whether well-formedness check failures are
/// reported via DATA_INVARIANT violations or exceptions.
void goto_functiont::validate(const namespacet &ns, const validation_modet vm)
  const
{
  // function body must end with an END_FUNCTION instruction
  if(body_available())
  {
    DATA_CHECK(
      vm,
      body.instructions.back().is_end_function(),
      "last instruction should be of end function type");
  }

  body.validate(ns, vm);

  find_symbols_sett typetags;
  find_type_symbols(type, typetags);
  const symbolt *symbol;
  for(const auto &identifier : typetags)
  {
    DATA_CHECK(
      vm, !ns.lookup(identifier, symbol), id2string(identifier) + " not found");
  }

  // Check that a void function does not contain any RETURN instructions
  if(to_code_type(type).return_type().id() == ID_empty)
  {
    forall_goto_program_instructions(instruction, body)
    {
      DATA_CHECK(
        vm,
        !instruction->is_return(),
        "void function should not return a value");
    }
  }

  validate_full_type(type, ns, vm);
}

bool is_mem_op(const irept &irep)
{
  return (
    irep.id() == "memcmp" || irep.id() == "memcpy" || irep.id() == "memset" ||
    irep.id() == "__builtin___memcpy_chk" ||
    irep.id() == "__builtin___memset_chk");
}

json_objectt
show_goto_instruction_json(const goto_programt::instructiont &instruction)
{
  std::stringstream ss;
  ss << format(instruction.get_function_call());
  const std::string &func_call = ss.str();

  json_objectt json_instr{
    {"instruction",
     json_objectt{
       {"functionCall", json_stringt(func_call)},
       {"sourceLocation", json(instruction.code.source_location())}}}};

  return json_instr;
}

xmlt show_goto_instruction_xml(const goto_programt::instructiont &instruction)
{
  xmlt xml_instr{"instruction"};

  std::stringstream ss;
  ss << format(instruction.get_function_call());
  const std::string &func_call = ss.str();

  xmlt &xml_function_call = xml_instr.new_element("function_call");
  xml_function_call.data = func_call;
  xml_instr.new_element(xml(instruction.code.source_location()));

  return xml_instr;
}

void show_goto_instruction(
  const goto_programt::instructiont &instruction,
  ui_message_handlert &ui_message_handler)
{
  ui_message_handlert::uit ui = ui_message_handler.get_ui();
  messaget msg(ui_message_handler);

  switch(ui)
  {
  case ui_message_handlert::uit::XML_UI:
  {
    msg.status() << show_goto_instruction_xml(instruction);
  }
  break;
  case ui_message_handlert::uit::JSON_UI:
  {
    msg.status() << show_goto_instruction_json(instruction);
  }
  break;
  case ui_message_handlert::uit::PLAIN:
  {
    msg.status() << messaget::faint << "\n"
                 << instruction.code.source_location().as_string()
                 << messaget::reset << messaget::eom;
    msg.status() << format(instruction.get_function_call()) << messaget::eom;
  }
  break;
  }
}

size_t
goto_functiont::get_memop_calls(ui_message_handlert &ui_message_handler) const
{
  size_t memop_count = 0;
  for(const auto &instruction : body.instructions)
  {
    if(instruction.type == FUNCTION_CALL)
    {
      auto called_function = instruction.get_function_call().function();

      if(is_mem_op(called_function.find(ID_identifier)))
      {
        memop_count++;
        show_goto_instruction(instruction, ui_message_handler);
      }
    }
  }
  return memop_count;
}
