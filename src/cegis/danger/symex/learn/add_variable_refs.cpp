#include <algorithm>

#include <util/cprover_prefix.h>
#include <util/arith_tools.h>

#include <ansi-c/c_types.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/symex/learn/add_variable_refs.h>

namespace
{
goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const char * const ops_array, const exprt &rhs, const unsigned int id)
{
  const goto_programt::targett target=body.insert_after(pos);
  goto_programt::instructiont &set_op=*target;
  set_op.type=ASSIGN;
  set_op.source_location=default_danger_source_location();
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
  return set_ops_reference(st, body, pos, DANGER_OPS, rhs, id);
}

goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const irep_idt &name, const unsigned int id)
{
  return set_ops_reference(st, body, pos, DANGER_OPS, name, id);
}

null_pointer_exprt get_null()
{
  const void_typet void_type;
  const pointer_typet void_pointer_type(void_type);
  return null_pointer_exprt(void_pointer_type);
}

template<class itert>
itert pred(itert it)
{
  return --it;
}

void link_user_symbols(const symbol_tablet &st, danger_variable_idst &var_ids,
    size_t &variable_id, bool consts)
{
  typedef symbol_tablet::symbolst symbolst;
  const symbolst &symbols=st.symbols;
  for (symbolst::const_iterator it=symbols.begin(); it != symbols.end(); ++it)
  {
    const symbolt &symbol=it->second;
    if (!is_danger_user_variable(symbol.name, symbol.type)) continue;
    const bool is_const=is_global_const(symbol.name, symbol.type);
    if (is_const == consts)
      var_ids.insert(std::make_pair(symbol.name, variable_id++));
  }
}

void link_user_program_variables(danger_programt &prog,
    const danger_variable_idst &var_ids)
{
  danger_variable_idst to_instrument(var_ids);
  goto_programt &body=get_danger_body(prog.gf);
  goto_programt::instructionst &instrs=body.instructions;
  const goto_programt::targett end=prog.danger_range.end;
  const symbol_tablet &st=prog.st;
  for (goto_programt::targett it=instrs.begin(); it != end; ++it)
  {
    goto_programt::instructiont &instr=*it;
    const goto_program_instruction_typet type=instr.type;
    if (DECL != type && DEAD != type) continue;
    const irep_idt &name=get_affected_variable(instr);
    if (!is_danger_user_variable(name, typet())) continue;
    const danger_variable_idst::const_iterator id=var_ids.find(name);
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
  const goto_programt::targett range_begin(prog.danger_range.begin);
  goto_programt::targett pos=pred(range_begin);
  danger_variable_idst::const_iterator it;
  for (it=to_instrument.begin(); it != to_instrument.end(); ++it)
  {
    pos=set_ops_reference(st, body, pos, it->first, it->second);
    if (it == to_instrument.begin()) move_labels(body, range_begin, pos);
  }
}

goto_programt::targett set_rops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const irep_idt &name, const unsigned int id)
{
  return set_ops_reference(st, body, pos, DANGER_RESULT_OPS, name, id);
}

goto_programt::targett link_temps(const symbol_tablet &st, goto_programt &body,
    goto_programt::targett pos, const size_t num_temps,
    const size_t num_user_vars)
{
  goto_programt::targett previous_successor(pos);
  ++previous_successor;
  for (size_t i=0; i < num_temps; ++i)
  {
    const std::string name=get_danger_meta_name(get_tmp(i));
    pos=set_rops_reference(st, body, pos, name, i);
    if (i == 0) move_labels(body, previous_successor, pos);
    pos=set_ops_reference(st, body, pos, name, i + num_user_vars);
  }
  return pos;
}

class link_single_resultt
{
  const symbol_tablet &st;
  goto_programt &body;
  const size_t num_user_vars;
  const size_t max_solution_size;
public:
  link_single_resultt(const symbol_tablet &st, goto_functionst &gf,
      const size_t num_user_vars, const size_t max_solution_size) :
      st(st), body(get_danger_body(gf)), num_user_vars(num_user_vars), max_solution_size(
          max_solution_size)
  {
  }

  void operator()(goto_programt::targett pos) const
  {
    const size_t num_temps=max_solution_size - 1;
    pos=link_temps(st, body, --pos, num_temps, num_user_vars);
    ++pos;
    set_rops_reference(st, body, pos, get_affected_variable(*pos), num_temps);
  }
};

void link_skolem(danger_programt &prog, const size_t num_user_vars,
    const size_t user_vars, const size_t max_solution_size,
    const danger_programt::loopt &loop)
{
  const goto_programt::targetst &sklm=loop.meta_variables.Sx;
  if (sklm.empty()) return;
  const symbol_tablet &st=prog.st;
  goto_programt &body=get_danger_body(prog.gf);
  goto_programt::targett pos=sklm.front();
  const size_t num_skolem=sklm.size();
  const size_t num_tmp=max_solution_size - num_skolem;
  link_temps(st, body, --pos, num_tmp, user_vars);
  goto_programt::targetst::const_iterator it=sklm.begin();
  for (size_t i=0; i < num_skolem - 1; ++i, ++it)
  {
    pos=*it;
    const goto_programt::instructiont &instr=*pos;
    const size_t id=num_tmp + i;
    const irep_idt &variable=get_affected_variable(instr);
    pos=set_rops_reference(st, body, pos, variable, id);
    pos=set_ops_reference(st, body, pos, variable, id + num_user_vars);
  }
  pos=sklm.back();
  const size_t final_id=max_solution_size - 1;
  set_rops_reference(st, body, pos, get_affected_variable(*pos), final_id);
}

class link_meta_variablest
{
  danger_programt &prog;
  const size_t user_vars;
  const size_t max_size;
public:
  link_meta_variablest(danger_programt &prog, const size_t num_user_vars,
      const size_t max_solution_size) :
      prog(prog), user_vars(num_user_vars), max_size(max_solution_size)
  {
  }

  void operator()(const danger_programt::loopt &loop) const
  {
    const danger_programt::meta_vars_positionst &meta=loop.meta_variables;
    const link_single_resultt inv(prog.st, prog.gf, user_vars, max_size);
    inv(meta.Dx);
    inv(meta.Dx_prime);
    const link_single_resultt &link_ranking=inv; // XXX: Lexicographical ranking?
    std::for_each(meta.Rx.begin(), meta.Rx.end(), link_ranking);
    std::for_each(meta.Rx_prime.begin(), meta.Rx_prime.end(), link_ranking);
    link_skolem(prog, user_vars, user_vars, max_size, loop);
  }
};

void link_meta_variables(danger_programt &prog, const size_t user_vars,
    const size_t max_solution_size)
{
  const symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  const link_single_resultt single(st, gf, user_vars, max_solution_size);
  single(prog.Dx0);
  const danger_programt::loopst &loops=prog.loops;
  const link_meta_variablest link(prog, user_vars, max_solution_size);
  std::for_each(loops.begin(), loops.end(), link);
}
}

void danger_add_variable_refs(danger_programt &prog,
    const danger_variable_idst &ids, const size_t max_solution_size)
{
  link_user_program_variables(prog, ids);
  link_meta_variables(prog, ids.size(), max_solution_size);
}

size_t get_danger_variable_ids(const symbol_tablet &st,
    danger_variable_idst &ids)
{
  size_t variable_id=0;
  link_user_symbols(st, ids, variable_id, true);
  const size_t num_consts=ids.size();
  link_user_symbols(st, ids, variable_id, false);
  return num_consts;
}
