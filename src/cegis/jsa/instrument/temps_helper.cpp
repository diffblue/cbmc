/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>
#include <ansi-c/c_types.h>

#include <goto-programs/remove_returns.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/instrument/temps_helper.h>

namespace
{
bool is_tmp(const symbol_tablet::symbolst::value_type &symbol)
{
  return std::string::npos != id2string(symbol.first).find(JSA_TMP_PREFIX);
}
}

goto_programt::targett zero_jsa_temps(jsa_programt &prog,
    goto_programt::targett pos)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  for(const symbol_tablet::symbolst::value_type &symbol : st.symbols)
  {
    if(!is_tmp(symbol)) continue;
    const symbol_exprt lhs(symbol.second.symbol_expr());
    pos=jsa_assign(st, gf, pos, lhs, from_integer(0, lhs.type()));
  }
  return pos;
}

void add_zero_jsa_temps_to_pred_exec(jsa_programt &prog)
{
  symbol_tablet &st=prog.st;
  const size_t num_tmps=count_tmps(st);
  assert(num_tmps > 0);
  goto_functionst::function_mapt &fm=prog.gf.function_map;
  const goto_functionst::function_mapt::iterator it=fm.find(JSA_PRED_EXEC);
  assert(fm.end() != it);
  goto_function_templatet<goto_programt> &exec=it->second;
  assert(exec.body_available());
  goto_programt &body=exec.body;
  goto_programt::instructionst &instr=body.instructions;
  source_locationt loc;
  loc.set_file(JSA_MODULE);
  loc.set_function(JSA_PRED_EXEC);
  for(goto_programt::targett pos=instr.begin(); pos != instr.end(); ++pos)
  {
    const codet &code=pos->code;
    if(ID_assign != code.get_statement()) continue;
    const code_assignt &assign=to_code_assign(code);
    const exprt &lhs=assign.lhs();
    if(ID_symbol != lhs.id()) continue;
    const symbol_exprt &symbol=to_symbol_expr(lhs);
    const irep_idt &id=symbol.get_identifier();
    if(std::string::npos == id2string(id).find(RETURN_VALUE_SUFFIX)) continue;
    const goto_programt::targett return_pos(pos);
    std::advance(pos, -1);
    const symbol_exprt ops(st.lookup(JSA_PRED_RES_OPS).symbol_expr());
    for(size_t i=1; i <= num_tmps; ++i)
    {
      const constant_exprt index(from_integer(i, signed_int_type()));
      const index_exprt elem(ops, index);
      const dereference_exprt lhs(elem, jsa_word_type());
      const exprt rhs(from_integer(0, lhs.type()));
      pos=cegis_assign(st, body, pos, lhs, rhs, loc);
    }
    move_labels(body, return_pos, pos);
    return;
  }
  assert(!"insertion point for temp assignment in " JSA_PRED_EXEC "not found");
}

size_t count_tmps(const symbol_tablet &st)
{
  return std::count_if(st.symbols.begin(), st.symbols.end(), is_tmp);
}
