/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/ui_message.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_convert.h>

#include <ansi-c/c_types.h>
#include <ansi-c/cprover_library.h>

#include <cegis/options/literals.h>

namespace {
const char EXECUTE[]="__CPROVER_synthesis_execute";

symbol_typet get_instr_type()
{
  return symbol_typet(SYNTHESIS_INSTR_TYPE_SYMBOL_NAME);
}

void add_synthesis_placeholder(symbol_tablet &symbol_table)
{
  if (symbol_table.has_symbol(EXECUTE)) return;
  symbolt symbol;
  symbol.name=EXECUTE;
  code_typet type;
  type.return_type()=void_typet();
  /*type.parameter_identifiers().push_back("prog_size");
  type.parameter_identifiers().push_back("prog");
  const code_typet::parametert prog_size(unsigned_int_type());
  type.parameters().push_back(prog_size);
  const pointer_typet instr_ptr_type(get_instr_type());
  const code_typet::parametert prog(instr_ptr_type);
  type.parameters().push_back(prog);*/
  symbol.type=type;
  symbol_table.add(symbol);
}
}

void add_cegis_library(symbol_tablet &symbol_table,
    goto_functionst &goto_functions, message_handlert &msg)
{
  std::set<irep_idt> synthesis_library;
  synthesis_library.insert(EXECUTE);
  add_synthesis_placeholder(symbol_table);
  add_cprover_library(synthesis_library, symbol_table, msg);
  goto_functionst::function_mapt &fm(goto_functions.function_map);
  goto_functionst::goto_functiont &execute=fm[EXECUTE];
  execute.body_available=true;
  const symbolt &execute_symbol=symbol_table.lookup(EXECUTE);
  goto_convert(to_code(execute_symbol.value), symbol_table, execute.body, msg);
  execute.body.add_instruction(END_FUNCTION);
  goto_functions.update();
}
