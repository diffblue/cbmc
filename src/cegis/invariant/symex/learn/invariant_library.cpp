#include <util/expr_util.h>

#include <goto-programs/goto_convert_functions.h>

#include <ansi-c/c_types.h>
#include <ansi-c/cprover_library.h>

#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/meta/literals.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/instrument/meta_variables.h>

namespace
{
const char BASE_NAME_SEP[]="::";
const char PROGRAM_ARG_BASE_NAME[]="program";
const char SIZE_ARG_BASE_NAME[]="size";

pointer_typet instr_type()
{
  return pointer_typet(symbol_typet(CEGIS_INSTRUCTION_TYPE_NAME));
}

void add_placeholder(symbol_tablet &symbol_table, const std::string &func_name)
{
  if (symbol_table.has_symbol(func_name)) return;
  symbolt symbol;
  symbol.name=func_name;
  symbol.base_name=symbol.name;
  symbol.pretty_name=symbol.base_name;
  code_typet type;
  type.return_type()=void_typet();
  type.parameter_identifiers().push_back(PROGRAM_ARG_BASE_NAME);
  type.parameter_identifiers().push_back(SIZE_ARG_BASE_NAME);
  code_typet::parametert program(instr_type());
  std::string program_arg(func_name);
  program_arg+=BASE_NAME_SEP;
  program_arg+=PROGRAM_ARG_BASE_NAME;
  program.set_identifier(program_arg);
  program.set_base_name(PROGRAM_ARG_BASE_NAME);
  type.parameters().push_back(program);
  code_typet::parametert size(unsigned_char_type());
  std::string size_arg(func_name);
  size_arg+=BASE_NAME_SEP;
  size_arg+=SIZE_ARG_BASE_NAME;
  size.set_identifier(size_arg);
  size.set_base_name(SIZE_ARG_BASE_NAME);
  type.parameters().push_back(size);
  symbol.type=type;
  symbol.is_lvalue=true;
  symbol.mode=ID_C;
  symbol.module=CEGIS_MODULE;
  symbol_table.add(symbol);
}

void set_loop_id(goto_functionst &gf, const std::string &func_name)
{
  goto_functionst::function_mapt &fm=gf.function_map;
  goto_functionst::function_mapt::iterator execute=fm.find(func_name);
  assert(fm.end() != execute);
  goto_programt &body=execute->second.body;
  goto_programt::instructionst &instrs=body.instructions;
  unsigned loop_number=0;
  for (goto_programt::targett it=instrs.begin(); it != instrs.end(); ++it)
  {
    goto_programt::instructiont &instr=*it;
    if (instr.is_backwards_goto()) instr.loop_number=loop_number++;
  }
}

goto_programt::targett init_array(const symbol_tablet &st, goto_programt &body,
    const char * const name, goto_programt::targett pos)
{
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSIGN;
  pos->source_location=default_invariant_source_location();
  const symbol_exprt array(st.lookup(name).symbol_expr());
  const array_typet &type=to_array_type(array.type());
  pos->code=code_assignt(array, array_of_exprt(gen_zero(type.subtype()), type));
  return pos;
}

void set_init_values(invariant_programt &prog)
{
  goto_programt &body=get_entry_body(prog.gf);
  goto_programt::targett pos=prog.invariant_range.begin;
  const symbol_tablet &st=prog.st;
  pos=init_array(st, body, CEGIS_OPS, --pos);
  pos=init_array(st, body, CEGIS_RESULT_OPS, pos);
}

std::string get_prefix(const size_t num_vars, const size_t num_consts,
    const size_t max_solution_size)
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
}

std::string get_invariant_library_text(const size_t num_vars,
    const size_t num_consts, const size_t max_solution_size,
    const std::string &func_name)
{
  symbol_tablet st;
  add_placeholder(st, func_name);
  std::set<irep_idt> functions;
  functions.insert(func_name);
  std::string text;
  //get_cprover_library_text(text, functions, st,
  //    get_prefix(num_vars, num_consts, max_solution_size));
  return text;
}

void add_invariant_library(invariant_programt &prog, message_handlert &msg,
    const size_t num_vars, const size_t num_consts,
    const size_t max_solution_size, const std::string &func_name)
{
  symbol_tablet &st=prog.st;
  goto_functionst &goto_functions=prog.gf;
  add_placeholder(st, func_name);
  std::set<irep_idt> functions;
  functions.insert(func_name);
  const std::string prefix(get_prefix(num_vars, num_consts, max_solution_size));
  //add_cprover_library(functions, st, msg, prefix);
  goto_convert(func_name, st, goto_functions, msg);
  set_loop_id(goto_functions, func_name);
  set_init_values(prog);
}
