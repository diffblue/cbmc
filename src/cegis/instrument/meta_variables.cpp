/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>

#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/instrument/meta_variables.h>

#define NS_SEP "::"

namespace
{
std::string concat(std::string lhs, const std::string &rhs)
{
  lhs+= NS_SEP;
  return lhs+=rhs;
}
}

std::string get_cegis_meta_name(const std::string &base_name)
{
  return concat(id2string(goto_functionst::entry_point()), base_name);
}

std::string get_local_meta_name(const std::string &func, const std::string &var)
{
  return concat(func, var);
}

namespace
{
void declare_local_var(goto_programt::instructiont &instr,
    const symbolt &symbol)
{
  instr.type=goto_program_instruction_typet::DECL;
  instr.code=code_declt(symbol.symbol_expr());
  instr.source_location=default_cegis_source_location();
}

goto_programt::targett declare_local_var(goto_programt &body,
    goto_programt::targett pos, const symbolt &symbol)
{
  pos=body.insert_after(pos);
  declare_local_var(*pos, symbol);
  return pos;
}
}

goto_programt::targett declare_cegis_meta_variable(symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &pos,
    const std::string &base_name, const typet &type)
{
  const std::string symbol_name(get_cegis_meta_name(base_name));
  const symbolt &symbol=create_cegis_symbol(st, symbol_name, type);
  return declare_local_var(get_entry_body(gf), pos, symbol);
}

goto_programt::targett declare_local_meta_variable(symbol_tablet &st,
    const std::string &fn, goto_programt &body,
    const goto_programt::targett &insert_after_pos, const std::string &bn,
    const typet &t)
{
  const symbolt &smb=create_cegis_symbol(st, get_local_meta_name(fn, bn), t);
  return declare_local_var(body, insert_after_pos, smb);
}

void declare_local_meta_variable(symbol_tablet &st, const std::string &fn,
    goto_programt::instructiont &instr, const std::string &bn, const typet &t)
{
  const symbolt &smb=create_cegis_symbol(st, get_local_meta_name(fn, bn), t);
  declare_local_var(instr, smb);
}

goto_programt::targett assign_cegis_meta_variable(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const std::string &base_name, const exprt &value)
{
  const std::string name(get_cegis_meta_name(base_name));
  return cegis_assign_user_variable(st, gf, insert_after_pos, name, value);
}

typet cegis_default_integer_type()
{
  return unsigned_int_type();
}

std::string get_cegis_code_prefix(const size_t num_vars,
    const size_t num_consts, const size_t max_solution_size)
{
  std::string prefix("#define " CEGIS_PREFIX "number_of_vars ");
  prefix+=integer2string(num_vars);
  prefix+="\n#define " CEGIS_PREFIX "number_of_consts ";
  prefix+=integer2string(num_consts);
  prefix+="u\n#define " CEGIS_PREFIX "number_of_ops ";
  prefix+=integer2string(num_vars + max_solution_size);
  prefix+="u\n#define " CEGIS_PREFIX "max_solution_size ";
  prefix+=integer2string(max_solution_size);
  return prefix+="u\n";
}

const symbolt &declare_global_meta_variable(symbol_tablet &st,
    const std::string &name, const typet &type)
{
  symbolt new_symbol;
  new_symbol.name=name;
  new_symbol.type=type;
  new_symbol.base_name=name;
  new_symbol.pretty_name=name;
  new_symbol.location=default_cegis_source_location();
  new_symbol.mode=ID_C;
  new_symbol.module=CEGIS_MODULE;
  new_symbol.is_lvalue=true;
  new_symbol.is_static_lifetime=true;
  new_symbol.is_state_var=true;
  assert(!st.add(new_symbol));
  return st.lookup(name);
}

const symbolt &declare_global_meta_variable(symbol_tablet &st,
    goto_functionst &gf, const std::string &name, const exprt &value)
{
  const symbolt &symbol=declare_global_meta_variable(st, name, value.type());
  goto_programt &init_body=get_body(gf, CPROVER_INIT);
  goto_programt::instructionst &instrs=init_body.instructions;
  goto_programt::targett pos=instrs.begin();
  if(instrs.size() >= 2) pos=std::prev(init_body.instructions.end(), 2);
  const symbol_exprt lhs(symbol.symbol_expr());
  cegis_assign(st, init_body, pos, lhs, value, default_cegis_source_location());
  return symbol;
}
