#include <algorithm>

#include <util/type_eq.h>
#include <goto-programs/goto_functions.h>

#include <cegis/instrument/literals.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/cegis-util/program_helper.h>

goto_programt &get_entry_body(goto_functionst &gf)
{
  const irep_idt id(goto_functionst::entry_point());
  goto_functionst::function_mapt &function_map=gf.function_map;
  const goto_functionst::function_mapt::iterator it=function_map.find(id);
  assert(function_map.end() != it && "Danger program function missing.");
  goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available() && "Danger program function body missing.");
  return f.body;
}

const goto_programt &get_entry_body(const goto_functionst &gf)
{
  const irep_idt id(goto_functionst::entry_point());
  const goto_functionst::function_mapt &function_map=gf.function_map;
  const goto_functionst::function_mapt::const_iterator it=function_map.find(id);
  assert(function_map.end() != it && "Danger program function missing.");
  const goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available() && "Danger program function body missing.");
  return f.body;
}

class goto_programt &get_body(
    class goto_functionst &gf,
    const std::string &func_name)
{
  const irep_idt id(func_name);
  goto_functionst::function_mapt &function_map=gf.function_map;
  const goto_functionst::function_mapt::iterator it=function_map.find(id);
  assert(function_map.end() != it && "Danger program function missing.");
  goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available() && "Danger program function body missing.");
  return f.body;
}

const goto_programt &get_body(
    const goto_functionst &gf,
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

bool is_nondet(const goto_programt::targett &target,
    const goto_programt::targett &end)
{
  const goto_programt::instructiont &instr=*target;
  switch (instr.type)
  {
  case goto_program_instruction_typet::DECL:
  {
    goto_programt::targett next=std::next(target);
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

void move_labels(goto_programt &body, const goto_programt::targett &from,
    const goto_programt::targett &to)
{
  for (goto_programt::instructiont &instr : body.instructions)
    for (goto_programt::targett &target : instr.targets)
      if (from == target) target=to;
}

bool is_builtin(const source_locationt &loc)
{
  if (loc.is_nil()) return true;
  const std::string &file=id2string(loc.get_file());
  return file.empty() || file.at(0) == '<';
}

symbolt &create_cegis_symbol(symbol_tablet &st, const std::string &full_name,
    const typet &type)
{
  symbolt new_symbol;
  new_symbol.name=full_name;
  new_symbol.type=type;
  new_symbol.base_name=full_name;
  new_symbol.pretty_name=new_symbol.base_name;
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

goto_programt::targett cegis_assign(const symbol_tablet &st,
    goto_functionst &gf, const goto_programt::targett &insert_after_pos,
    const exprt &lhs, const exprt &rhs, const source_locationt &loc)
{
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett assign=body.insert_after(insert_after_pos);
  assign->type=goto_program_instruction_typet::ASSIGN;
  assign->source_location=loc;
  const namespacet ns(st);
  const typet &type=lhs.type();
  if (type_eq(type, rhs.type(), ns)) assign->code=code_assignt(lhs, rhs);
  else assign->code=code_assignt(lhs, typecast_exprt(rhs, type));
  return assign;
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
