/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <functional>

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/options/jsa_program_info.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/learn/insert_predicates_and_queries.h>

#define PRED_SIZES "__CPROVER_JSA_PREDICATE_SIZES"

namespace
{
goto_programt::targett assume_less_than(goto_programt &body,
    goto_programt::targett pos, const exprt &lhs, const size_t max)
{
  pos=body.insert_after(pos);
  pos->source_location=jsa_builtin_source_location();
  pos->type=goto_program_instruction_typet::ASSUME;
  const constant_exprt max_expr(from_integer(max, jsa_internal_index_type()));
  const binary_relation_exprt size_limit(lhs, ID_le, max_expr);
  const exprt min(from_integer(1, jsa_internal_index_type()));
  const binary_relation_exprt min_size(lhs, ID_ge, min);
  pos->guard=and_exprt(min_size, size_limit);
  return pos;
}

void declare_size_and_prog(jsa_programt &prog, const std::string &prog_name,
    const std::string &size_name,
    const std::function<array_typet(const exprt &)> type_factory,
    const size_t max_size)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett &pos=prog.synthetic_variables;
  pos=body.insert_after(pos);
  declare_jsa_meta_variable(st, pos, size_name, jsa_internal_index_type());
  const irep_idt &size_id=get_affected_variable(*pos);
  const symbol_exprt sz_expr(st.lookup(size_id).symbol_expr());
  pos=assume_less_than(body, pos, sz_expr, max_size);
  pos=body.insert_after(pos);
  const constant_exprt array_sz_expr(from_integer(max_size, sz_expr.type()));
  declare_jsa_meta_variable(st, pos, prog_name, type_factory(array_sz_expr));
}
}

void declare_jsa_predicates(jsa_programt &prog, const size_t max_sz)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  goto_programt &body=get_entry_body(gf);
  const symbol_exprt preds(st.lookup(JSA_PREDS).symbol_expr());
  const symbol_exprt pred_sizes(st.lookup(PRED_SIZES).symbol_expr());
  const bv_arithmetict bv(to_array_type(preds.type()).size());
  const mp_integer::ullong_t num_preds=bv.to_integer().to_ulong();
  const typet sz_type(signed_int_type());
  const exprt zero(from_integer(0, sz_type));
  const size_t max_pred_size=get_max_pred_size(st);
  for (mp_integer::ullong_t i=0; i < num_preds; ++i)
  {
    goto_programt::targett &pos=prog.synthetic_variables;
    std::string base_name(JSA_PRED_PREFIX);
    base_name+=std::to_string(i);
    const std::string sz_name(base_name + JSA_SIZE_SUFFIX);
    declare_size_and_prog(prog, base_name, sz_name, jsa_predicate_type, max_pred_size);
    const constant_exprt index(from_integer(i, sz_type));
    const index_exprt preds_elem(preds, index);
    const std::string local_pred_name(get_cegis_meta_name(base_name));
    const symbol_exprt &local_pred(st.lookup(local_pred_name).symbol_expr());
    const index_exprt local_preds_elem(local_pred, zero);
    pos=jsa_assign(st, gf, pos, preds_elem, address_of_exprt(local_preds_elem));
    const index_exprt pred_sizes_elem(pred_sizes, index);
    const symbolt &sz_symb(st.lookup(get_cegis_meta_name(sz_name)));
    pos=jsa_assign(st, gf, pos, pred_sizes_elem, sz_symb.symbol_expr());
    pos=body.insert_after(pos);
    pos->type=goto_program_instruction_typet::FUNCTION_CALL;
    pos->source_location=jsa_builtin_source_location();
    code_function_callt call;
    call.function()=st.lookup(JSA_ASSUME_VALID_PRED).symbol_expr();
    call.arguments().push_back(index);
    pos->code=call;
  }
}

void declare_jsa_query(jsa_programt &prog, const size_t max_size)
{
  declare_size_and_prog(prog, JSA_QUERY, JSA_QUERY_SZ, jsa_query_type,
      get_max_query_size(prog.st));
}

void declare_jsa_invariant(jsa_programt &prog, const size_t max_size)
{
  declare_size_and_prog(prog, JSA_INV, JSA_INV_SZ, jsa_invariant_type, 1);
}
