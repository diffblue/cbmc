#include <util/expr_util.h>

#include <goto-programs/goto_convert_functions.h>

#include <ansi-c/c_types.h>
#include <ansi-c/cprover_library.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/util/danger_program_helper.h>

namespace
{
const char PROGRAM_ARG_NAME[]="__CPROVER_danger_execute::program";
const char PROGRAM_ARG_BASE_NAME[]="program";
const char SIZE_ARG_NAME[]="__CPROVER_danger_execute::size";
const char SIZE_ARG_BASE_NAME[]="size";

pointer_typet instr_type()
{
  return pointer_typet(symbol_typet(DANGER_INSTRUCTION_TYPE_NAME));
}

void add_placeholder(symbol_tablet &symbol_table)
{
  if (symbol_table.has_symbol(DANGER_EXECUTE)) return;
  symbolt symbol;
  symbol.name=DANGER_EXECUTE;
  symbol.base_name=symbol.name;
  symbol.pretty_name=symbol.base_name;
  code_typet type;
  type.return_type()=void_typet();
  type.parameter_identifiers().push_back(PROGRAM_ARG_BASE_NAME);
  type.parameter_identifiers().push_back(SIZE_ARG_BASE_NAME);
  code_typet::parametert program(instr_type());
  program.set_identifier(PROGRAM_ARG_NAME);
  program.set_base_name(PROGRAM_ARG_BASE_NAME);
  type.parameters().push_back(program);
  code_typet::parametert size(unsigned_char_type());
  size.set_identifier(SIZE_ARG_NAME);
  size.set_base_name(SIZE_ARG_BASE_NAME);
  type.parameters().push_back(size);
  symbol.type=type;
  symbol.is_lvalue=true;
  symbol.mode=ID_C;
  symbol.module=DANGER_MODULE;
  symbol_table.add(symbol);
}

void set_loop_id(goto_functionst &gf)
{
  goto_functionst::function_mapt &fm=gf.function_map;
  goto_functionst::function_mapt::iterator execute=fm.find(DANGER_EXECUTE);
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
  pos->source_location=default_danger_source_location();
  const symbol_exprt array(st.lookup(name).symbol_expr());
  const array_typet &type=to_array_type(array.type());
  pos->code=code_assignt(array, array_of_exprt(gen_zero(type.subtype()), type));
  return pos;
}

void set_init_values(danger_programt &prog)
{
  goto_programt &body=get_danger_body(prog.gf);
  goto_programt::targett pos=prog.danger_range.begin;
  const symbol_tablet &st=prog.st;
  pos=init_array(st, body, DANGER_OPS, --pos);
  pos=init_array(st, body, DANGER_RESULT_OPS, pos);
}

std::string get_prefix(const size_t num_vars, const size_t num_consts,
    const size_t max_solution_size)
{
  std::string prefix("#define __CPROVER_danger_number_of_vars ");
  prefix+=integer2string(num_vars);
  prefix+="\n#define __CPROVER_danger_number_of_consts ";
  prefix+=integer2string(num_consts);
  prefix+="u\n#define __CPROVER_danger_number_of_ops ";
  prefix+=integer2string(num_vars + max_solution_size);
  prefix+="u\n#define __CPROVER_danger_max_solution_size ";
  prefix+=integer2string(max_solution_size);
  return prefix+="u\n";
}
}

std::string get_danger_library_text(const size_t num_vars,
    const size_t num_consts, const size_t max_solution_size)
{
  symbol_tablet st;
  add_placeholder(st);
  std::set<irep_idt> functions;
  functions.insert(DANGER_EXECUTE);
  std::string text;
  #if 0
  get_cprover_library_text(text, functions, st,
      get_prefix(num_vars, num_consts, max_solution_size));
  #endif
  return text;
}

void add_danger_library(danger_programt &prog, message_handlert &msg,
    const size_t num_vars, const size_t num_consts,
    const size_t max_solution_size)
{
  symbol_tablet &st=prog.st;
  goto_functionst &goto_functions=prog.gf;
  add_placeholder(st);
  std::set<irep_idt> functions;
  functions.insert(DANGER_EXECUTE);
  const std::string prefix(get_prefix(num_vars, num_consts, max_solution_size));
  #if 0
  add_cprover_library(functions, st, msg, prefix);
  #endif
  goto_convert(DANGER_EXECUTE, st, goto_functions, msg);
  set_loop_id(goto_functions);
  set_init_values(prog);
}
