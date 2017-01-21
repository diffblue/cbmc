#include <algorithm>
#include <functional>

#include <util/type_eq.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/remove_returns.h>

#include <cegis/instrument/literals.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/program_helper.h>

goto_programt &get_entry_body(goto_functionst &gf)
{
  return get_body(gf, id2string(goto_functionst::entry_point()));
}

const goto_programt &get_entry_body(const goto_functionst &gf)
{
  return get_body(gf, id2string(goto_functionst::entry_point()));
}

goto_programt &get_body(goto_functionst &gf, const std::string &func_name)
{
  const irep_idt id(func_name);
  goto_functionst::function_mapt &function_map=gf.function_map;
  const goto_functionst::function_mapt::iterator it=function_map.find(id);
  assert(function_map.end() != it && "Danger program function missing.");
  goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available() && "Danger program function body missing.");
  return f.body;
}

goto_programt &get_body(goto_functionst &gf,
    const goto_programt::const_targett pos)
{
  return get_body(gf, id2string(pos->function));
}

const goto_programt &get_body(const goto_functionst &gf,
    const std::string &func_name)
{
  const irep_idt id(func_name);
  const goto_functionst::function_mapt &function_map=gf.function_map;
  const goto_functionst::function_mapt::const_iterator it=function_map.find(id);
  assert(function_map.end() != it && "Danger program function missing.");
  const goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available() && "Danger program function body missing.");
  return f.body;
}

namespace
{
class id_searcht: public const_expr_visitort
{
  const irep_idt &id;
  bool found;
public:
  id_searcht(const irep_idt &id) :
      id(id), found(false)
  {
  }

  virtual ~id_searcht()
  {
  }

  virtual void operator()(const exprt &expr)
  {
    if (ID_symbol != expr.id() || found) return;
    if (id == to_symbol_expr(expr).get_identifier()) found=true;
  }

  bool is_found()
  {
    return found;
  }
};

bool contains(const exprt &rhs, const irep_idt &id)
{
  id_searcht search(id);
  rhs.visit(search);
  return search.is_found();
}
}

bool is_nondet(goto_programt::const_targett target,
    goto_programt::const_targett end)
{
  const goto_programt::instructiont &instr=*target;
  switch (instr.type)
  {
  case goto_program_instruction_typet::DECL:
  {
    goto_programt::const_targett next=std::next(target);
    if (next == end) return true;
    if (goto_program_instruction_typet::FUNCTION_CALL == next->type)
    {
      if (to_code_function_call(next->code).lhs().is_not_nil()) return false;
      else ++next;
    }
    const goto_programt::instructiont next_instr=*next;
    if (goto_program_instruction_typet::ASSIGN != next_instr.type) return true;
    const irep_idt id(get_affected_variable(instr));
    if (id != get_affected_variable(next_instr)) return true;
    return contains(to_code_assign(next_instr.code).rhs(), id);
  }
  case goto_program_instruction_typet::ASSIGN:
  {
    const exprt &rhs=to_code_assign(instr.code).rhs();
    if (ID_side_effect != rhs.id()) return false;
    return ID_nondet == to_side_effect_expr(rhs).get_statement();
  }
  case goto_program_instruction_typet::FUNCTION_CALL:
  {
    const code_function_callt &call=to_code_function_call(instr.code);
    if (call.lhs().is_not_nil()) return false;
  }
  default:
    return false;
  }
}

bool is_return_value_name(const std::string &name)
{
  return contains(name, "return_value___")
      || contains(name, RETURN_VALUE_SUFFIX);
}

const typet &get_affected_type(const goto_programt::instructiont &instr)
{
  switch (instr.type)
  {
  case goto_program_instruction_typet::DECL:
    return to_code_decl(instr.code).symbol().type();
  case goto_program_instruction_typet::ASSIGN:
    return to_code_assign(instr.code).lhs().type();
  case goto_program_instruction_typet::DEAD:
    return to_code_dead(instr.code).symbol().type();
  default:
    assert(!"Only DECL, ASSIGN, DEAD allowed.");
  }
}

const irep_idt &get_affected_variable(const goto_programt::instructiont &instr)
{
  switch (instr.type)
  {
  case goto_program_instruction_typet::DECL:
    return to_code_decl(instr.code).get_identifier();
  case goto_program_instruction_typet::ASSIGN:
    return to_symbol_expr(to_code_assign(instr.code).lhs()).get_identifier();
  case goto_program_instruction_typet::DEAD:
    return to_code_dead(instr.code).get_identifier();
  default:
    assert(!"Only DECL, ASSIGN, DEAD allowed.");
  }
}

goto_programt::targetst find_nondet_instructions(goto_programt &body)
{
  goto_programt::targetst result;
  goto_programt::instructionst &instrs=body.instructions;
  const goto_programt::targett end(instrs.end());
  for (goto_programt::targett it=instrs.begin(); it != end; ++it)
    if (is_nondet(it, end)) result.push_back(it);
  return result;
}

namespace
{
const char NS_SEP[]="::";
}
bool is_global_const(const irep_idt &name, const typet &type)
{
  if (!type.get_bool(ID_C_constant)) return false;
  const std::string &n=id2string(name);
  if (std::string::npos != n.find(CEGIS_CONSTANT_PREFIX)) return true;
  return std::string::npos == n.find(NS_SEP);
}

void move_labels(goto_programt::instructionst &body,
    const goto_programt::targett &from, const goto_programt::targett &to)
{
  for (goto_programt::instructiont &instr : body)
    for (goto_programt::targett &target : instr.targets)
      if (from == target) target=to;
}

void move_labels(goto_programt &body, const goto_programt::targett &from,
    const goto_programt::targett &to)
{
  move_labels(body.instructions, from, to);
}

goto_programt::targett insert_before_preserve_labels(goto_programt &body,
    const goto_programt::targett &target)
{
  const goto_programt::targett result=body.insert_before(target);
  move_labels(body, target, result);
  return result;
}

bool is_builtin(const source_locationt &loc)
{
  if (loc.is_nil()) return true;
  const std::string &file=id2string(loc.get_file());
  return file.empty() || file.at(0) == '<';
}

symbolt &create_local_cegis_symbol(symbol_tablet &st,
    const std::string &full_name, const std::string &base_name,
    const typet &type)
{
  symbolt new_symbol;
  new_symbol.name=full_name;
  new_symbol.type=type;
  new_symbol.base_name=base_name;
  new_symbol.pretty_name=base_name;
  new_symbol.location=default_cegis_source_location();
  new_symbol.mode=ID_C;
  new_symbol.module=CEGIS_MODULE;
  new_symbol.is_thread_local=true;
  new_symbol.is_static_lifetime=false;
  new_symbol.is_file_local=true;
  new_symbol.is_lvalue=true;
  assert(!st.add(new_symbol));
  return st.lookup(new_symbol.name);
}

symbolt &create_cegis_symbol(symbol_tablet &st, const std::string &full_name,
    const typet &type)
{
  return create_local_cegis_symbol(st, full_name, full_name, type);
}

void cegis_assign(const symbol_tablet &st, goto_programt::instructiont &instr,
    const exprt &lhs, const exprt &rhs, const source_locationt &loc)
{
  instr.type=goto_program_instruction_typet::ASSIGN;
  instr.source_location=loc;
  const namespacet ns(st);
  const typet &type=lhs.type();
  if (type_eq(type, rhs.type(), ns)) instr.code=code_assignt(lhs, rhs);
  else instr.code=code_assignt(lhs, typecast_exprt(rhs, type));
}

goto_programt::targett cegis_assign(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &insert_after_pos,
    const exprt &lhs, const exprt &rhs, const source_locationt &loc)
{
  const goto_programt::targett assign=body.insert_after(insert_after_pos);
  cegis_assign(st, *assign, lhs, rhs, loc);
  return assign;
}

goto_programt::targett cegis_assign(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const exprt &lhs, const exprt &rhs, const source_locationt &loc)
{
  goto_programt &body=get_entry_body(gf);
  return cegis_assign(st, body, insert_after_pos, lhs, rhs, loc);
}

goto_programt::targett cegis_assign(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const exprt &lhs, const exprt &rhs)
{
  return cegis_assign(st, gf, insert_after_pos, lhs, rhs,
      default_cegis_source_location());
}

goto_programt::targett cegis_assign_user_variable(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const irep_idt &name, const exprt &value)
{
  const symbol_exprt lhs(st.lookup(name).symbol_expr());
  return cegis_assign(st, gf, insert_after_pos, lhs, value);
}

goto_programt::targett cegis_assign_local_variable(const symbol_tablet &st,
    goto_programt &body, const goto_programt::targett &insert_after_pos,
    const std::string &func_name, const std::string &var_name,
    const exprt &value)
{
  std::string name(func_name);
  name+=NS_SEP;
  name+=var_name;
  const symbol_exprt lhs(st.lookup(name).symbol_expr());
  const source_locationt loc(default_cegis_source_location());
  return cegis_assign(st, body, insert_after_pos, lhs, value, loc);
}

symbol_exprt get_ret_val_var(const irep_idt &func_id, const typet &type)
{
  return symbol_exprt(id2string(func_id) + RETURN_VALUE_SUFFIX, type);
}

void remove_return(goto_programt &body, const goto_programt::targett pos)
{
  code_function_callt &call=to_code_function_call(pos->code);
  const irep_idt &id=to_symbol_expr(call.function()).get_identifier();
  const typet &type=call.lhs().type();
  const source_locationt &loc=pos->source_location;
  const irep_idt &func=pos->function;
  const goto_programt::targett assign=body.insert_after(pos);
  assign->make_assignment();
  assign->source_location=loc;
  assign->code=code_assignt(call.lhs(), get_ret_val_var(id, type));
  assign->function=func;
  call.lhs().make_nil();
}

goto_programt::targett add_return_assignment(goto_programt &body,
    goto_programt::targett pos, const irep_idt &func_id, const exprt &value)
{
  const source_locationt &loc=pos->source_location;
  pos=body.insert_after(pos);
  pos->make_assignment();
  pos->source_location=loc;
  pos->code=code_assignt(get_ret_val_var(func_id, value.type()), value);
  return pos;
}

namespace
{
goto_programt::targett insert_preserving_source_location(
    goto_programt::targett pos,
    const std::function<goto_programt::targett(goto_programt::targett)> &inserter)
{
  const source_locationt &loc=pos->source_location;
  const irep_idt &func_name=pos->function;
  pos=inserter(pos);
  pos->source_location=loc;
  pos->function=func_name;
  return pos;
}
}

goto_programt::targett insert_after_preserving_source_location(
    goto_programt &body, goto_programt::targett pos)
{
  const auto op=std::bind1st(std::mem_fun(&goto_programt::insert_after), &body);
  return insert_preserving_source_location(pos, op);
}

goto_programt::targett insert_before_preserving_source_location(
    goto_programt &body, goto_programt::targett pos)
{
  typedef goto_programt::targett (goto_programt::*ftype)(
      goto_programt::targett);
  const auto op=std::bind1st(
      std::mem_fun(static_cast<ftype>(&goto_programt::insert_before)), &body);
  return insert_preserving_source_location(pos, op);
}

void assign_in_cprover_init(goto_functionst &gf, symbolt &symbol,
    const exprt &value)
{
  symbol.value=value;
  goto_programt &body=get_body(gf, CPROVER_INIT);
  goto_programt::instructionst &instrs=body.instructions;
  const auto p(std::mem_fun_ref(&goto_programt::instructiont::is_end_function));
  goto_programt::targett pos=std::find_if(instrs.begin(), instrs.end(), p);
  assert(instrs.end() != pos);
  pos=insert_before_preserving_source_location(body, pos);
  pos->type=goto_program_instruction_typet::ASSIGN;
  const symbol_exprt lhs(symbol.symbol_expr());
  pos->code=code_assignt(lhs, value);
}
