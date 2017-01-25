/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/instrument/literals.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/symex/learn/instrument_vars.h>

#if 0
namespace
{
null_pointer_exprt get_null()
{
  const pointer_typet void_pointer_type=pointer_typet(void_typet());
  return null_pointer_exprt(void_pointer_type);
}
}
#endif

void link_result_var(const symbol_tablet &st, goto_functionst &gf,
    const size_t num_user_vars, const size_t max_solution_size,
    goto_programt::targett pos)
{
  goto_programt &body=get_entry_body(gf);
  const size_t num_temps=max_solution_size - 1;
  pos=link_temp_vars(st, body, --pos, num_temps, num_user_vars);
  ++pos;
  set_rops_reference(st, body, pos, get_affected_variable(*pos), num_temps);
}

goto_programt::targett set_rops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const irep_idt &name, const unsigned int id)
{
  return set_ops_reference(st, body, pos, CEGIS_RESULT_OPS, name, id);
}

goto_programt::targett link_temp_vars(const symbol_tablet &st,
    goto_programt &body, goto_programt::targett pos, const size_t num_temps,
    const size_t num_user_vars)
{
  goto_programt::targett previous_successor(pos);
  ++previous_successor;
  for (size_t i=0; i < num_temps; ++i)
  {
    const std::string name=get_cegis_meta_name(get_tmp(i));
    pos=set_rops_reference(st, body, pos, name, i);
    if (i == 0) move_labels(body, previous_successor, pos);
    pos=set_ops_reference(st, body, pos, name, i + num_user_vars);
  }
  return pos;
}

void link_user_program_variables(invariant_programt &prog,
    const operand_variable_idst &var_ids)
{
  const goto_programt::targett begin=prog.invariant_range.begin;
  const goto_programt::targett end=prog.invariant_range.end;
  link_user_program_variable_ops(prog.st, prog.gf, var_ids,
      is_instrumentable_user_variable, begin, end);
}

#if 0
namespace
{
void link_user_symbols(const symbol_tablet &st, operand_variable_idst &var_ids,
    size_t &variable_id, bool consts)
{
  typedef symbol_tablet::symbolst symbolst;
  const symbolst &symbols=st.symbols;
  for (symbolst::const_iterator it=symbols.begin(); it != symbols.end(); ++it)
  {
    const symbolt &symbol=it->second;
    if (!is_instrumentable_user_variable(symbol.name, symbol.type)) continue;
    const bool is_const=is_global_const(symbol.name, symbol.type);
    if (is_const == consts)
      var_ids.insert(std::make_pair(symbol.name, variable_id++));
  }
}
}
#endif

size_t get_invariant_variable_ids(const symbol_tablet &st,
    operand_variable_idst &ids)
{
  return get_variable_op_ids(st, ids, &is_instrumentable_user_variable);
}
