/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <goto-programs/goto_convert_functions.h>

#include <ansi-c/c_types.h>
#include <ansi-c/cprover_library.h>

#include <linking/zero_initializer.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/invariant/options/invariant_program.h>

namespace
{
const char BASE_NAME_SEP[]="::";
const char PROGRAM_ARG_BASE_NAME[]="program";
const char SIZE_ARG_BASE_NAME[]="size";

pointer_typet instr_type()
{
  return pointer_typet(symbol_typet(CEGIS_INSTRUCTION_TYPE_NAME));
}

code_typet cegis_execute_type()
{
  code_typet type;
  type.return_type()=void_typet();
  type.parameter_identifiers().push_back(PROGRAM_ARG_BASE_NAME);
  type.parameter_identifiers().push_back(SIZE_ARG_BASE_NAME);
  code_typet::parametert program(instr_type());
  std::string program_arg(CEGIS_EXECUTE);
  program_arg+=BASE_NAME_SEP;
  program_arg+=PROGRAM_ARG_BASE_NAME;
  program.set_identifier(program_arg);
  program.set_base_name(PROGRAM_ARG_BASE_NAME);
  type.parameters().push_back(program);
  code_typet::parametert size(unsigned_char_type());
  std::string size_arg(CEGIS_EXECUTE);
  size_arg+=BASE_NAME_SEP;
  size_arg+=SIZE_ARG_BASE_NAME;
  size.set_identifier(size_arg);
  size.set_base_name(SIZE_ARG_BASE_NAME);
  type.parameters().push_back(size);
  return type;
}

void add_execute_placeholder(symbol_tablet &symbol_table,
    const std::string &func_name, const code_typet &type)
{
  if(symbol_table.has_symbol(func_name)) return;
  symbolt symbol;
  symbol.name=func_name;
  symbol.base_name=symbol.name;
  symbol.pretty_name=symbol.base_name;
  symbol.type=type;
  symbol.is_lvalue=true;
  symbol.mode=ID_C;
  symbol.module=CEGIS_MODULE;
  symbol_table.add(symbol);
}

goto_programt::targett init_array(const symbol_tablet &st, goto_programt &body,
    const char * const name, goto_programt::targett pos)
{
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSIGN;
  pos->source_location=default_cegis_source_location();
  const symbol_exprt array(st.lookup(name).symbol_expr());
  const array_typet &type=to_array_type(array.type());
  const namespacet ns(st);
  pos->code=
    code_assignt(
      array,
      zero_initializer(type, pos->source_location, ns));
  return pos;
}

void set_init_values(const symbol_tablet &st, goto_functionst &gf)
{
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett pos=body.instructions.begin();
  pos=init_array(st, body, CEGIS_OPS, pos);
  init_array(st, body, CEGIS_RESULT_OPS, pos);
}
}

std::string get_cegis_library_text(const size_t num_vars,
    const size_t num_consts, const size_t max_size,
    const std::string &func_name)
{
  symbol_tablet st;
  add_execute_placeholder(st, func_name, cegis_execute_type());
  std::set<irep_idt> functions;
  functions.insert(func_name);
  std::string text(get_cegis_code_prefix(num_vars, num_consts, max_size));
  return text+=get_cprover_library_text(functions, st);
}

void add_cegis_library(symbol_tablet &st, goto_functionst &gf,
    message_handlert &msg, const size_t num_vars, const size_t num_consts,
    const size_t max_solution_size, const std::string &func_name)
{
  add_execute_placeholder(st, func_name, cegis_execute_type());
  std::set<irep_idt> functions;
  functions.insert(func_name);
  const std::string library_src(
      get_cegis_library_text(num_vars, num_consts, max_solution_size,
          func_name));

  add_library(library_src, st, msg);
  goto_convert(func_name, st, gf, msg);
  gf.compute_loop_numbers();
  gf.update();
  set_init_values(st, gf);
}

void add_cegis_execute_placeholder(symbol_tablet &st)
{
  add_execute_placeholder(st, CEGIS_EXECUTE, cegis_execute_type());
}
