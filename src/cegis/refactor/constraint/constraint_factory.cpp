/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/config.h>
#include <util/expr_util.h>
#include <util/message.h>
#include <goto-programs/goto_convert_functions.h>
#include <java_bytecode/java_entry_point.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/refactor/instructionset/processor_symbols.h>
#include <cegis/refactor/instructionset/processor_types.h>
#include <cegis/refactor/options/refactor_program.h>

namespace
{
code_typet create_func_type()
{
  code_typet result;
  result.return_type()=empty_typet();
  return result;
}

void create_or_redirect_entry(symbol_tablet &st, goto_functionst &gf)
{
  typedef goto_functionst::function_mapt fmapt;
  fmapt &fmap=gf.function_map;
  const fmapt::const_iterator it=fmap.find(goto_functionst::entry_point());
  null_message_handlert msg;
  if (fmap.end() == it)
  {
    config.main=CONSTRAINT_CALLER;
    assert(!java_entry_point(st, ID_empty, msg, false, 0));
    goto_convert(CPROVER_INIT, st, gf, msg);
    goto_convert(goto_functionst::entry_point(), st, gf, msg);
  } else
  {
    // TODO: Implement
    assert(false);
  }
}

void add_to_symbol_table(symbol_tablet &st, const std::string &name,
    const goto_functionst::function_mapt::mapped_type &func)
{
  if (st.has_symbol(name)) return;
  symbolt new_symbol;
  new_symbol.name=name;
  new_symbol.type=func.type;
  new_symbol.base_name=name;
  new_symbol.pretty_name=name;
  new_symbol.location=default_cegis_source_location();
  new_symbol.mode=ID_C;
  new_symbol.module=CEGIS_MODULE;
  new_symbol.value=code_blockt();
  assert(!st.add(new_symbol));
}
}

void create_constraint_function_caller(refactor_programt &prog)
{
  goto_functionst &gf=prog.gf;
  const char * const func_name=CONSTRAINT_CALLER_ID;
  goto_functionst::function_mapt::mapped_type &func=gf.function_map[func_name];
  func.type=create_func_type();
  goto_programt &body=func.body;
  const source_locationt loc(default_cegis_source_location());
  symbol_tablet &st=prog.st;
  for (const refactor_programt::sketcht &sketch : prog.sketches)
  {
    const symbolt &symbol=st.lookup(sketch.init->function);
    const code_typet &type=to_code_type(symbol.type);
    goto_programt::targett pos=body.add_instruction(
        goto_program_instruction_typet::FUNCTION_CALL);
    pos->source_location=loc;
    code_function_callt call;
    call.function()=symbol.symbol_expr();
    code_function_callt::argumentst &args=call.arguments();
    for (const code_typet::parametert &param : type.parameters())
      args.push_back(gen_zero(param.type()));
    pos->code=call;
  }
  body.add_instruction(goto_program_instruction_typet::END_FUNCTION);
  body.update();
  add_to_symbol_table(st, func_name, func);
  create_or_redirect_entry(st, gf);
}

#define CLONE_SUFFIX "_CLONE"
#define INIT_SUFFIX "_INIT"

namespace
{
const goto_ranget &get_first_range(const refactor_programt::sketcht &sketch)
{
  const size_t input_dist=std::distance(sketch.init, sketch.input_range.first);
  const size_t spec_dist=std::distance(sketch.init, sketch.spec_range.first);
  return input_dist < spec_dist ? sketch.input_range : sketch.spec_range;
}

const goto_ranget &get_second_range(const refactor_programt::sketcht &sketch)
{
  const size_t input_dist=std::distance(sketch.init, sketch.input_range.first);
  const size_t spec_dist=std::distance(sketch.init, sketch.spec_range.first);
  return input_dist >= spec_dist ? sketch.input_range : sketch.spec_range;
}

void make_skip(const goto_programt::targett first,
    const goto_programt::targett last)
{
  std::for_each(first, last, [](goto_programt::instructiont &instr)
  { if(!instr.is_decl()) instr.make_skip();});
}

void link_refactoring_ranges(goto_programt &body,
    const refactor_programt::sketcht &sketch)
{
  goto_programt::instructionst &instrs=body.instructions;
  make_skip(instrs.begin(), sketch.init);
  sketch.init->make_skip();
  const goto_ranget &first=get_first_range(sketch);
  const goto_ranget &second=get_second_range(sketch);
  make_skip(first.second, second.first);
  make_skip(second.second, std::prev(instrs.end()));
}

goto_programt::targett nondet_init(const symbol_tablet &st, goto_programt &body,
    goto_programt::targett pos, const irep_idt &state_var)
{
  const symbolt &symbol=st.lookup(state_var);
  if (!is_cegis_primitive(symbol.type)) return pos; // TODO: Handle class types
  pos=insert_after_preserving_source_location(body, pos);
  pos->type=goto_program_instruction_typet::ASSIGN;
  const symbol_exprt lhs(symbol.symbol_expr());
  const side_effect_expr_nondett rhs(lhs.type());
  pos->code=code_assignt(lhs, rhs);
  return pos;
}

goto_programt::targett havoc_inputs(const symbol_tablet &st,
    goto_programt &body, const refactor_programt::sketcht &sketch)
{
  goto_programt::targett pos=sketch.init;
  for (const irep_idt &state_var : sketch.state_vars)
    pos=nondet_init(st, body, pos, state_var);
  return pos;
}

std::string get_clone_name(const irep_idt &id, const char * const suffix)
{
  std::string result(id2string(id));
  return result+=suffix;
}

std::string get_clone_id(const irep_idt &id, const std::string &func,
    const char * suffix)
{
  return get_local_meta_name(func, get_clone_name(id, suffix));
}

goto_programt::targett create_snapshot(symbol_tablet &st, goto_programt &body,
    const std::string &func_name, const std::set<irep_idt> &state_vars,
    goto_programt::targett pos, const char * const suffix)
{
  for (const irep_idt &state_var : state_vars)
  {
    const symbolt &symbol=st.lookup(state_var);
    const typet &type=symbol.type;
    if (!is_cegis_primitive(type)) continue; // TODO: Handle class types (clone)
    const std::string clone_name(get_clone_name(symbol.base_name, suffix));
    pos=declare_local_meta_variable(st, func_name, body, pos, clone_name, type);
    const symbol_exprt rhs(symbol.symbol_expr());
    pos=cegis_assign_local_variable(st, body, pos, func_name, clone_name, rhs);
  }
  return pos;
}

void create_init_snapshot(symbol_tablet &st, goto_programt &body,
    const refactor_programt::sketcht &sketch, const goto_programt::targett pos)
{
  if (sketch.state_vars.empty()) return;
  const std::string func(id2string(sketch.init->function));
  create_snapshot(st, body, func, sketch.state_vars, pos, INIT_SUFFIX);
}

goto_programt::targett create_baseline_snapshot(symbol_tablet &st,
    goto_programt &body, const refactor_programt::sketcht &sketch)
{
  const goto_ranget &range=get_second_range(sketch);
  goto_programt::targett pos=std::prev(range.first);
  const std::string func(id2string(sketch.init->function));
  return create_snapshot(st, body, func, sketch.state_vars, pos, CLONE_SUFFIX);
}

void assign_init_snapshot(symbol_tablet &st, goto_programt &body,
    const refactor_programt::sketcht &sketch, goto_programt::targett pos)
{
  const std::string &func=id2string(sketch.init->function);
  for (const irep_idt &var : sketch.state_vars)
  {
    const symbolt &symbol=st.lookup(var);
    if (!is_cegis_primitive(symbol.type)) continue; // TODO: Handle class types
    const symbol_exprt lhs(symbol.symbol_expr());
    const irep_idt &base_name=symbol.base_name;
    const std::string rhs_name(get_clone_id(base_name, func, INIT_SUFFIX));
    const symbol_exprt rhs(st.lookup(rhs_name).symbol_expr());
    pos=cegis_assign(st, body, pos, lhs, rhs, pos->source_location);
  }
}

equal_exprt equal_to_clone(const symbol_tablet &st, const irep_idt &func_name,
    const irep_idt &state_var)
{
  const symbolt &symbol=st.lookup(state_var);
  const symbol_exprt lhs(symbol.symbol_expr());
  const irep_idt &base_name=symbol.base_name;
  const std::string fn(id2string(func_name));
  const std::string clone_var(get_clone_id(base_name, fn, CLONE_SUFFIX));
  const symbol_exprt rhs(st.lookup(clone_var).symbol_expr());
  return equal_exprt(lhs, rhs);
}

void insert_assertion(/*const */symbol_tablet &st, goto_programt &body,
    const refactor_programt::sketcht &sketch)
{
  const irep_idt &func_name=sketch.init->function;
  exprt::operandst clauses;
  for (const irep_idt &var : sketch.state_vars)
  {
    if (!is_cegis_primitive(st.lookup(var).type)) continue; // TODO: Handle class types
    if (is_refactor_meta_var(var)) continue;
    clauses.push_back(equal_to_clone(st, func_name, var));
  }
  goto_programt::targett pos=get_second_range(sketch).second;
  pos=insert_after_preserving_source_location(body, pos);
  pos->type=goto_program_instruction_typet::ASSERT;
  pos->guard=conjunction(clauses);
}
}

void create_refactoring_constraint(refactor_programt &prog)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  for (const refactor_programt::sketcht &sketch : prog.sketches)
  {
    goto_programt &body=get_body(gf, sketch.init);
    link_refactoring_ranges(body, sketch);
    goto_programt::targett pos=havoc_inputs(st, body, sketch);
    create_init_snapshot(st, body, sketch, pos);
    pos=create_baseline_snapshot(st, body, sketch);
    assign_init_snapshot(st, body, sketch, pos);
    insert_assertion(st, body, sketch);
    body.update();
    body.compute_loop_numbers();
  }
}
