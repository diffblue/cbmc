/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>
#include <util/expr_util.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/instrument/temps_helper.h>
#include <cegis/jsa/preprocessing/clone_heap.h>
#include <cegis/jsa/learn/execute_jsa_programs.h>

#define EXEC_FULL "__CPROVER_jsa_full_query_execute"
#define SYNC "__CPROVER_jsa_synchronise_iterator"

namespace
{
void make_constraint_call(const symbol_tablet &st, goto_functionst &gf,
    goto_programt::targett pos, const code_function_callt::argumentst &args)
{
  goto_programt &body=get_entry_body(gf);
  const symbol_exprt lhs(st.lookup(get_affected_variable(*pos)).symbol_expr());
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  pos->source_location=jsa_builtin_source_location();
  code_function_callt call;
  call.lhs()=lhs;
  call.function()=st.lookup(JSA_INV_EXEC).symbol_expr();
  call.arguments()=args;
  pos->code=call;
  remove_return(body, pos);
}

void make_constraint_call(const symbol_tablet &st, goto_functionst &gf,
    const goto_programt::targett &pos)
{
  code_function_callt::argumentst args;
  args.push_back(address_of_exprt(get_user_heap(gf)));
  args.push_back(address_of_exprt(get_queried_heap(st)));
  const symbol_exprt p(st.lookup(get_cegis_meta_name(JSA_INV)).symbol_expr());
  args.push_back(address_of_exprt(index_exprt(p, gen_zero(signed_int_type()))));
  args.push_back(st.lookup(get_cegis_meta_name(JSA_INV_SZ)).symbol_expr());
  make_constraint_call(st, gf, pos, args);
}

void make_query_call(jsa_programt &prog, const symbol_tablet &st,
    goto_functionst &gf, goto_programt::targett pos,
    const bool full_query=false)
{
  goto_programt &body=get_entry_body(gf);
  pos=insert_before_preserve_labels(body, pos);
  const goto_programt::targett temps_end=zero_jsa_temps(prog, pos);
  if (pos != temps_end)
  {
    move_labels(body, pos, std::next(pos));
    body.instructions.erase(pos);
    pos=body.insert_after(temps_end);
  }
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  pos->source_location=jsa_builtin_source_location();
  code_function_callt call;
  call.function()=
      st.lookup(full_query ? EXEC_FULL : JSA_QUERY_EXEC).symbol_expr();
  code_function_callt::argumentst &args=call.arguments();
  args.push_back(address_of_exprt(get_queried_heap(st)));
  const symbol_exprt p(st.lookup(get_cegis_meta_name(JSA_QUERY)).symbol_expr());
  args.push_back(address_of_exprt(index_exprt(p, gen_zero(signed_int_type()))));
  args.push_back(st.lookup(get_cegis_meta_name(JSA_QUERY_SZ)).symbol_expr());
  pos->code=call;
}

void make_sync_call(const symbol_tablet &st, goto_functionst &gf,
    goto_programt::targett pos)
{
  goto_programt &body=get_entry_body(gf);
  pos=insert_before_preserve_labels(body, pos);
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  pos->source_location=jsa_builtin_source_location();
  code_function_callt call;
  call.function()=st.lookup(SYNC).symbol_expr();
  code_function_callt::argumentst &args=call.arguments();
  args.push_back(address_of_exprt(get_user_heap(gf)));
  args.push_back(address_of_exprt(get_queried_heap(st)));
  const symbol_exprt p(st.lookup(get_cegis_meta_name(JSA_QUERY)).symbol_expr());
  args.push_back(address_of_exprt(index_exprt(p, gen_zero(signed_int_type()))));
  args.push_back(st.lookup(get_cegis_meta_name(JSA_QUERY_SZ)).symbol_expr());
  pos->code=call;
}
}

void execute_jsa_learn_programs(jsa_programt &prog)
{
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  make_constraint_call(st, gf, prog.base_case);
  make_query_call(prog, st, gf, prog.base_case);
  make_constraint_call(st, gf, prog.inductive_assumption);
  make_query_call(prog, st, gf, prog.inductive_assumption);
  make_constraint_call(st, gf, prog.inductive_step);
  make_sync_call(st, gf, prog.inductive_step);
  make_query_call(prog, st, gf, prog.inductive_step);
  make_constraint_call(st, gf, prog.property_entailment);
  make_query_call(prog, st, gf, prog.property_entailment, true);
  make_sync_call(st, gf, prog.property_entailment);
}
