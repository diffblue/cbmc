/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>
#include <util/type_eq.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/learn/instrument_pred_ops.h>

namespace
{
bool contains(const std::string &haystack, const char * const needle)
{
  return std::string::npos != haystack.find(needle);
}

bool is_pred_op_decl(const symbol_tablet &st, const goto_programt::targett &pos)
{
  if(goto_program_instruction_typet::DECL != pos->type) return false;
  const std::string &id=id2string(get_affected_variable(*pos));
  if(contains(id, JSA_TMP_PREFIX) || contains(id, JSA_LAMBDA_OP)
      || contains(id, JSA_CONSTANT_PREFIX)) return true;
  if(contains(id, CPROVER_PREFIX)) return false;
  const namespacet ns(st);
  const typet lhs(jsa_word_type());
  return type_eq(lhs, st.lookup(id).type, ns);
}
}

goto_programt::targetst collect_pred_ops(jsa_programt &prog)
{
  const symbol_tablet &st=prog.st;
  goto_programt::instructionst &body=get_entry_body(prog.gf).instructions;
  const goto_programt::targett end(prog.body.first);
  goto_programt::targetst pred_ops;
  for(goto_programt::targett it=body.begin(); it != end; ++it)
    if(is_pred_op_decl(st, it)) pred_ops.push_back(it);
  return pred_ops;
}

#define PRED_OPS "__CPROVER_JSA_PRED_OPS"
#define JSA_PRED_OP_COUNT "__CPROVER_JSA_PRED_OPS_COUNT"
#define JSA_PRED_RESULT_OP_COUNT "__CPROVER_JSA_PRED_RESULT_OPS_COUNT"

namespace
{
void mark_dead(goto_programt &body, goto_programt::targett pos,
    const index_exprt &op_elem)
{
  const irep_idt &id=get_affected_variable(*pos);
  goto_programt::instructionst &instrs=body.instructions;
  const goto_programt::targett end(instrs.end());
  pos=std::find_if(pos, end, [&id](const goto_programt::instructiont &instr)
  { return DEAD == instr.type && id == get_affected_variable(instr);});
  if(end == pos) return;
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::ASSIGN;
  pos->source_location=jsa_builtin_source_location();
  pos->code=code_assignt(op_elem, from_integer(0, op_elem.type()));
}
}

void instrument_pred_ops(jsa_programt &prog, const goto_programt::targetst &ops,
    pred_op_idst &op_ids, pred_op_idst &const_op_ids)
{
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_entry_body(gf);
  const symbol_exprt pred_ops(st.lookup(PRED_OPS).symbol_expr());
  const symbol_exprt pred_res_ops(st.lookup(JSA_PRED_RES_OPS).symbol_expr());
  const typet sz_type(signed_int_type());
  size_t op_index=0;
  size_t res_op_idx=0;
  for(const goto_programt::targett &op : ops)
  {
    const symbol_exprt var(st.lookup(get_affected_variable(*op)).symbol_expr());
    const address_of_exprt var_ptr(var);
    const_op_ids.insert(std::make_pair(op_index, var));
    const constant_exprt op_index_expr(from_integer(op_index++, sz_type));
    const index_exprt op_elem(pred_ops, op_index_expr);
    mark_dead(body, op, op_elem);
    goto_programt::targett pos=jsa_assign(st, gf, op, op_elem, var_ptr);
    if(!is_jsa_const(var))
    {
      op_ids.insert(std::make_pair(res_op_idx, var));
      const constant_exprt res_op_idx_expr(from_integer(res_op_idx++, sz_type));
      const index_exprt res_op_elem(pred_res_ops, res_op_idx_expr);
      mark_dead(body, op, res_op_elem);
      pos=jsa_assign(st, gf, pos, res_op_elem, address_of_exprt(var));
    }
    if(op == prog.synthetic_variables) prog.synthetic_variables=pos;
  }
  const symbol_exprt op_count(st.lookup(JSA_PRED_OP_COUNT).symbol_expr());
  const constant_exprt op_value(from_integer(op_index, op_count.type()));
  goto_programt::targett &pos=prog.synthetic_variables;
  pos=jsa_assign(st, gf, pos, op_count, op_value);
  const symbol_exprt res_cnt(st.lookup(JSA_PRED_RESULT_OP_COUNT).symbol_expr());
  const constant_exprt res_value(from_integer(res_op_idx, res_cnt.type()));
  pos=jsa_assign(st, gf, pos, res_cnt, res_value);
}

void instrument_pred_ops(jsa_programt &prog, const goto_programt::targetst &ops)
{
  pred_op_idst op_ids;
  pred_op_idst const_op_ids;
  instrument_pred_ops(prog, ops, op_ids, const_op_ids);
}
