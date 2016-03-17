#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include <cegis/invariant/meta/literals.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/invariant/instrument/meta_variables.h>
#include <cegis/invariant/symex/learn/instrument_vars.h>

namespace
{
null_pointer_exprt get_null()
{
  const pointer_typet void_pointer_type=pointer_typet(void_typet());
  return null_pointer_exprt(void_pointer_type);
}

goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const char * const ops_array, const exprt &rhs, const unsigned int id)
{
  const goto_programt::targett target=body.insert_after(pos);
  goto_programt::instructiont &set_op=*target;
  set_op.type=ASSIGN;
  set_op.source_location=default_invariant_source_location();
  const constant_exprt index(from_integer(id, unsigned_int_type()));
  const symbol_exprt ops(st.lookup(ops_array).symbol_expr());
  const index_exprt op(ops, index);
  set_op.code=code_assignt(op, rhs);
  return target;
}

goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const char * const ops_array, const irep_idt &name, const unsigned int id)
{
  const symbol_exprt rhs(st.lookup(name).symbol_expr());
  return set_ops_reference(st, body, pos, ops_array, address_of_exprt(rhs), id);
}

goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos, const exprt &rhs,
    const unsigned int id)
{
  return set_ops_reference(st, body, pos, CEGIS_OPS, rhs, id);
}
}

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

goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const irep_idt &name, const unsigned int id)
{
  return set_ops_reference(st, body, pos, CEGIS_OPS, name, id);
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
    const std::string name=get_invariant_meta_name(get_tmp(i));
    pos=set_rops_reference(st, body, pos, name, i);
    if (i == 0) move_labels(body, previous_successor, pos);
    pos=set_ops_reference(st, body, pos, name, i + num_user_vars);
  }
  return pos;
}

void link_user_program_variables(invariant_programt &prog,
    const invariant_variable_idst &var_ids)
{
  invariant_variable_idst to_instrument(var_ids);
  goto_programt &body=get_entry_body(prog.gf);
  goto_programt::instructionst &instrs=body.instructions;
  const goto_programt::targett end=prog.invariant_range.end;
  const symbol_tablet &st=prog.st;
  for (goto_programt::targett it=instrs.begin(); it != end; ++it)
  {
    goto_programt::instructiont &instr=*it;
    const goto_program_instruction_typet type=instr.type;
    if (DECL != type && DEAD != type) continue;
    const irep_idt &name=get_affected_variable(instr);
    if (!is_invariant_user_variable(name, typet())) continue;
    const invariant_variable_idst::const_iterator id=var_ids.find(name);
    switch (type)
    {
    case goto_program_instruction_typet::DECL:
      set_ops_reference(st, body, it, name, id->second);
      to_instrument.erase(id->first);
      break;
    case goto_program_instruction_typet::DEAD:
      //set_ops_reference(st, body, pred(it), get_null(), id->second);
      // XXX: pred(it) would be cleaner, but this avoids inconsistencies when jumping to DEAD.
      set_ops_reference(st, body, it, get_null(), id->second);
      break;
    default:
      break;
    }
  }
  const goto_programt::targett range_begin(prog.invariant_range.begin);
  goto_programt::targett pos=range_begin;
  --pos;
  invariant_variable_idst::const_iterator it;
  for (it=to_instrument.begin(); it != to_instrument.end(); ++it)
  {
    pos=set_ops_reference(st, body, pos, it->first, it->second);
    if (it == to_instrument.begin()) move_labels(body, range_begin, pos);
  }
}

namespace
{
void link_user_symbols(const symbol_tablet &st,
    invariant_variable_idst &var_ids, size_t &variable_id, bool consts)
{
  typedef symbol_tablet::symbolst symbolst;
  const symbolst &symbols=st.symbols;
  for (symbolst::const_iterator it=symbols.begin(); it != symbols.end(); ++it)
  {
    const symbolt &symbol=it->second;
    if (!is_invariant_user_variable(symbol.name, symbol.type)) continue;
    const bool is_const=is_global_const(symbol.name, symbol.type);
    if (is_const == consts)
      var_ids.insert(std::make_pair(symbol.name, variable_id++));
  }
}
}

size_t get_invariant_variable_ids(const symbol_tablet &st,
    invariant_variable_idst &ids)
{
  size_t variable_id=0;
  link_user_symbols(st, ids, variable_id, true);
  const size_t num_consts=ids.size();
  link_user_symbols(st, ids, variable_id, false);
  return num_consts;
}
