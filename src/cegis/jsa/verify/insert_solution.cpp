/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/value/jsa_solution.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/instrument/temps_helper.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/clone_heap.h>
#include <cegis/jsa/verify/insert_solution.h>

#define JSA_PRED_RESULT JSA_PREFIX "pred_result"
#define SYNC_IT "__CPROVER_jsa_verify_synchronise_iterator"
#define MAKE_NULL "__CPROVER_jsa__internal_make_null"

namespace
{
void add_predicates(jsa_programt &prog, const jsa_solutiont::predicatest &preds)
{
  assert(!preds.empty());
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_body(gf, JSA_PRED_EXEC);
  body.clear();
  goto_programt::instructionst &instrs=body.instructions;
  std::string pred_id_name(JSA_PRED_EXEC);
  pred_id_name+="::pred_id";
  const symbol_exprt pred_id(st.lookup(pred_id_name).symbol_expr());
  goto_programt::targett pos=body.insert_after(instrs.begin());
  declare_jsa_meta_variable(st, pos, JSA_PRED_RESULT, jsa_word_type());
  const std::string result(get_cegis_meta_name(JSA_PRED_RESULT));
  const symbol_exprt ret_val(st.lookup(result).symbol_expr());
  const goto_programt::targett first=pos;
  pos=add_return_assignment(body, pos, JSA_PRED_EXEC, ret_val);
  const goto_programt::targett end=pos;
  pos=body.insert_after(pos);
  pos->source_location=jsa_builtin_source_location();
  pos->type=goto_program_instruction_typet::END_FUNCTION;
  std::vector<goto_programt::targett> pred_begins;
  pos=first;
  size_t idx=0;
  for (const jsa_solutiont::predicatest::value_type &pred : preds)
  {
    assert(!pred.empty());
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    pos->source_location=jsa_builtin_source_location();
    const constant_exprt pred_idx_expr(from_integer(idx++, pred_id.type()));
    pos->guard=notequal_exprt(pred_id, pred_idx_expr);
    pred_begins.push_back(pos);
    pos=copy_instructions(instrs, pos, pred);
    const goto_programt::targett last_assign=std::prev(pos);
    const exprt &last_lhs=to_code_assign(last_assign->code).lhs();
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::ASSIGN;
    pos->source_location=jsa_builtin_source_location();
    pos->code=code_assignt(ret_val, last_lhs);
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::GOTO;
    pos->source_location=jsa_builtin_source_location();
    pos->targets.push_back(end);
  }
  assert(pred_begins.size() == preds.size());
  for (auto it=pred_begins.begin(); it != std::prev(pred_begins.end()); ++it)
  {
    const goto_programt::targett &pos=*it;
    pos->targets.push_back(*std::next(it));
  }
  pred_begins.back()->targets.push_back(end);
  add_zero_jsa_temps_to_pred_exec(prog);

  body.compute_incoming_edges();
  body.compute_target_numbers();
}

void insert_invariant(const symbol_tablet &st, const goto_functionst &gf, goto_programt &body,
    goto_programt::targett pos, const goto_programt::instructionst &prog)
{
  assert(prog.size() == 1);
  const symbol_exprt v(st.lookup(get_affected_variable(*pos)).symbol_expr());
  pos=body.insert_after(pos);
  pos->source_location=jsa_builtin_source_location();
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  code_function_callt call;
  call.lhs()=v;
  call.function()=st.lookup(JSA_INV_VERIFY_EXEC).symbol_expr();
  code_function_callt::argumentst &args=call.arguments();
  args.push_back(address_of_exprt(get_user_heap(gf)));
  args.push_back(address_of_exprt(get_queried_heap(st)));
  pos->code=call;
  remove_return(body, pos);
}

const exprt &get_iterator_arg(const codet &code)
{
  const code_function_callt &call=to_code_function_call(code);
  const code_function_callt::argumentst &args=call.arguments();
  assert(args.size() >= 3);
  return args.at(2);
}

void insert_sync_call(const symbol_tablet &st, const goto_functionst &gf,
    goto_programt &body, goto_programt::targett pos,
    const goto_programt::instructionst &query)
{
  assert(!query.empty());
  if (query.empty()) return;
  const exprt &it_arg=get_iterator_arg(query.front().code);
  code_function_callt sync;
  code_function_callt::argumentst &sync_args=sync.arguments();
  sync_args.push_back(address_of_exprt(get_user_heap(gf)));
  sync_args.push_back(address_of_exprt(get_queried_heap(st)));
  sync_args.push_back(it_arg);
  sync.function()=st.lookup(SYNC_IT).symbol_expr();
  pos=insert_before_preserve_labels(body, pos);
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  pos->source_location=jsa_builtin_source_location();
  pos->code=sync;
}

void make_full_query_call(const symbol_tablet &st, const goto_functionst &gf,
    goto_programt &body, goto_programt::targett pos,
    const goto_programt::instructionst &query)
{
  if (query.empty()) return;
  pos=insert_before_preserve_labels(body, pos);
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  pos->source_location=jsa_builtin_source_location();
  code_function_callt call;
  call.function()=st.lookup(MAKE_NULL).symbol_expr();
  code_function_callt::argumentst &args=call.arguments();
  args.push_back(address_of_exprt(get_user_heap(gf)));
  args.push_back(get_iterator_arg(query.front().code));
  pos->code=call;
}

void insert_before(jsa_programt &jsa_prog, goto_programt &body,
    const goto_programt::targett &pos, const goto_programt::instructionst &prog)
{
  if (prog.empty()) return;
  const goto_programt::targett insert_after=std::prev(pos);
  copy_instructions(body.instructions, insert_after, prog);
  zero_jsa_temps(jsa_prog, insert_after);
  move_labels(body, pos, std::next(insert_after));
}
}

void insert_jsa_solution(jsa_programt &prog, const jsa_solutiont &solution)
{
  add_predicates(prog, solution.predicates);
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_entry_body(gf);

  insert_before(prog, body, prog.base_case, solution.query);
  insert_invariant(st, gf, body, prog.base_case, solution.invariant);
  insert_before(prog, body, prog.inductive_assumption, solution.query);
  insert_invariant(st, gf, body, prog.inductive_assumption, solution.invariant);
  insert_sync_call(st, gf, body, prog.inductive_step, solution.query);
  insert_before(prog, body, prog.inductive_step, solution.query);
  insert_invariant(st, gf, body, prog.inductive_step, solution.invariant);
  make_full_query_call(st, gf, body, prog.property_entailment, solution.query);
  insert_before(prog, body, prog.property_entailment, solution.query);
  insert_sync_call(st, gf, body, prog.property_entailment, solution.query);
  insert_invariant(st, gf, body, prog.property_entailment, solution.invariant);

  body.compute_incoming_edges();
  body.compute_target_numbers();
}
