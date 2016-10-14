#include <util/namespace_utils.h>

#include <ansi-c/c_types.h>

#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/instrument/meta_variables.h>

namespace
{
const char NS_SEP[]="::";
}
std::string get_cegis_meta_name(const std::string &base_name)
{
  std::string name=id2string(goto_functionst::entry_point());
  name+=NS_SEP;
  return name+=base_name;
}

goto_programt::targett declare_cegis_meta_variable(symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &pos,
    const std::string &base_name, const typet &type)
{
  const std::string symbol_name(get_cegis_meta_name(base_name));
  create_cegis_symbol(st, symbol_name, type);
  const symbol_exprt symbol(symbol_name, type);
  const goto_programt::targett decl=get_entry_body(gf).insert_after(pos);
  decl->type=goto_program_instruction_typet::DECL;
  decl->code=code_declt(symbol);
  decl->source_location=default_cegis_source_location();
  return decl;
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
