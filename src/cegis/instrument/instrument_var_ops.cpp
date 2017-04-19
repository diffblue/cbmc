/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/cprover_prefix.h>
#include <util/arith_tools.h>
#include <ansi-c/c_types.h>

#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/instrument_var_ops.h>

namespace
{
bool is_cegis_constant(const irep_idt &name)
{
  return std::string::npos != id2string(name).find(CEGIS_CONSTANT_PREFIX);
}

void link_user_symbols(const symbol_tablet &st, operand_variable_idst &var_ids,
    size_t &variable_id, bool consts, const is_op_variablet is_op_variable)
{
  typedef symbol_tablet::symbolst symbolst;
  const symbolst &symbols=st.symbols;
  for(symbolst::const_iterator it=symbols.begin(); it != symbols.end(); ++it)
  {
    const symbolt &s=it->second;
    if(!is_op_variable(s.name, s.type)
        || (is_builtin(s.location) && !is_cegis_constant(s.name))) continue;
    const bool is_const=is_global_const(s.name, s.type);
    if(is_const == consts)
      var_ids.insert(std::make_pair(s.name, variable_id++));
  }
}

size_t get_min_id(const operand_variable_idst &ids)
{
  if(ids.empty()) return 0;
  return std::max_element(ids.begin(), ids.end(),
      [](const operand_variable_idst::value_type &lhs, const operand_variable_idst::value_type &rhs)
      { return lhs.second < rhs.second;})->second + 1;
}
}

size_t get_variable_op_ids(const symbol_tablet &st, operand_variable_idst &ids,
    const is_op_variablet is_op_variable)
{
  size_t variable_id=get_min_id(ids);
  link_user_symbols(st, ids, variable_id, true, is_op_variable);
  const size_t num_consts=ids.size();
  link_user_symbols(st, ids, variable_id, false, is_op_variable);
  return num_consts;
}

namespace
{
const char RETURN_VALUE_IDENTIFIER[]="#return_value";
}

bool is_instrumentable_user_variable(const irep_idt &id, const typet &type)
{
  if(ID_code == type.id()) return false;
  const std::string &name=id2string(id);
  if(std::string::npos != name.find("::")
      && std::string::npos == name.find(id2string(ID_main))
      && std::string::npos == name.find(id2string(goto_functionst::entry_point())))
    return false; // Inlined variables
  if(std::string::npos != name.find(RETURN_VALUE_IDENTIFIER)) return false;
  return std::string::npos == name.find(CPROVER_PREFIX);
}

size_t get_variable_op_ids(const symbol_tablet &st, operand_variable_idst &ids)
{
  return get_variable_op_ids(st, ids, &is_instrumentable_user_variable);
}

namespace
{
null_pointer_exprt get_null()
{
  const pointer_typet void_pointer_type=pointer_typet(void_typet());
  return null_pointer_exprt(void_pointer_type);
}
}

void link_user_program_variable_ops(const symbol_tablet &st,
    class goto_functionst &gf, const operand_variable_idst &var_ids,
    const is_op_variablet is_op_variable, const goto_programt::targett begin,
    const goto_programt::targett end)
{
  operand_variable_idst to_instrument(var_ids);
  goto_programt &body=get_entry_body(gf);
  goto_programt::instructionst &instrs=body.instructions;
  goto_programt::targett pos=begin;
  while(is_builtin(pos->source_location) && pos != end)
    ++pos;
  for(goto_programt::targett it=pos; it != end; ++it)
  {
    goto_programt::instructiont &instr=*it;
    const goto_program_instruction_typet type=instr.type;
    if(DECL != type && DEAD != type) continue;
    const irep_idt &name=get_affected_variable(instr);
    if(!is_op_variable(name, st.lookup(name).type)) continue;
    const operand_variable_idst::const_iterator id=var_ids.find(name);
    if(DEAD == type) set_ops_reference(st, body, it, get_null(), id->second);
    else
    {
      set_ops_reference(st, body, it, name, id->second);
      to_instrument.erase(id->first);
    }
  }
  if(pos != instrs.begin()) --pos;
  typedef operand_variable_idst::const_iterator itt;
  const itt first=to_instrument.begin();
  for(itt it=first; it != to_instrument.end(); ++it)
  {
    pos=set_ops_reference(st, body, pos, it->first, it->second);
    if(first == it) move_labels(body, begin, pos);
  }
}

void link_user_program_variable_ops(const symbol_tablet &st,
    class goto_functionst &gf, const operand_variable_idst &var_ids,
    const goto_programt::targett begin, const goto_programt::targett end)
{
  const is_op_variablet filter=&is_instrumentable_user_variable;
  link_user_program_variable_ops(st, gf, var_ids, filter, begin, end);
}

goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const char * const ops_array, const exprt &rhs, const unsigned int id)
{
  const goto_programt::targett target=body.insert_after(pos);
  goto_programt::instructiont &set_op=*target;
  set_op.type=ASSIGN;
  set_op.source_location=default_cegis_source_location();
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

goto_programt::targett set_ops_reference(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &pos,
    const irep_idt &name, const unsigned int id)
{
  return set_ops_reference(st, body, pos, CEGIS_OPS, name, id);
}

source_locationt default_cegis_source_location()
{
  source_locationt loc;
  loc.set_file(CEGIS_MODULE);
  loc.set_function(goto_functionst::entry_point());
  return loc;
}
