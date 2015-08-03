/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-programs/goto_functions.h>

#include <cegis/util/goto_program_adapter.h>
#include <cegis/options/literals.h>

goto_program_adaptert::goto_program_adaptert(symbol_tablet &symbol_table,
    goto_programt &goto_program) :
    symbol_table(symbol_table), goto_program(goto_program)
{
}

goto_program_adaptert::~goto_program_adaptert()
{
}

code_declt &goto_program_adaptert::append_decl(const irep_idt &identifier,
    const typet &type) const
{
  const nil_exprt value;
  const source_locationt location;
  return append_decl(identifier, type, value, location);
}

code_declt &goto_program_adaptert::append_decl(const irep_idt &identifier,
    const typet &type, const source_locationt &location) const
{
  const nil_exprt value;
  return append_decl(identifier, type, value, location);
}

code_declt &goto_program_adaptert::append_decl(const irep_idt &identifier,
    const typet &type, const exprt &value,
    const source_locationt &location) const
{
  symbolt new_symbol;
  new_symbol.name=identifier;
  new_symbol.type=type;
  new_symbol.base_name=new_symbol.name;
  new_symbol.location=location;
  new_symbol.mode=ID_C;
  new_symbol.module=SYNTHESIS_MODULE;
  new_symbol.is_thread_local=true;
  new_symbol.is_static_lifetime=false;
  new_symbol.is_file_local=true;
  new_symbol.is_lvalue=true;
  if (value.is_not_nil()) new_symbol.value=value;
  assert(!symbol_table.add(new_symbol));
  goto_programt::targett decl=goto_program.add_instruction(DECL);
  symbolt &symbol=symbol_table.lookup(identifier);
  decl->code=code_declt(symbol.symbol_expr());
  decl->source_location=location;
  return to_code_decl(decl->code);
}

goto_programt &get_program_body(goto_functionst &gf, const std::string &name)
{
  goto_functionst::function_mapt &fm(gf.function_map);
  const goto_functionst::function_mapt::iterator it=fm.find(name);
  assert(fm.end() != it);
  return it->second.body;
}

const goto_programt &get_program_body(const goto_functionst &gf,
    const std::string &name)
{
  const goto_functionst::function_mapt &fm(gf.function_map);
  const goto_functionst::function_mapt::const_iterator it=fm.find(name);
  assert(fm.end() != it);
  return it->second.body;
}
