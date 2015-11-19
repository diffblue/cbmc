#include <util/cprover_prefix.h>

#include <goto-programs/goto_functions.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/util/danger_program_helper.h>

goto_programt &get_danger_body(goto_functionst &gf)
{
  const irep_idt id(goto_functionst::entry_point());
  goto_functionst::function_mapt &function_map=gf.function_map;
  const goto_functionst::function_mapt::iterator it=function_map.find(id);
  assert(function_map.end() != it && "Danger program function missing.");
  goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available && "Danger program function body missing.");
  return f.body;
}

const goto_programt &get_danger_body(const goto_functionst &gf)
{
  const irep_idt id(goto_functionst::entry_point());
  const goto_functionst::function_mapt &function_map=gf.function_map;
  const goto_functionst::function_mapt::const_iterator it=function_map.find(id);
  assert(function_map.end() != it && "Danger program function missing.");
  const goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available && "Danger program function body missing.");
  return f.body;
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
    assert(false && "Only DECL and ASSIGN allowed.");
  }
}

bool is_nondet(const goto_programt::targett &target)
{
  const goto_programt::instructiont &instr=*target;
  switch (instr.type)
  {
  case goto_program_instruction_typet::DECL:
  {
    goto_programt::targett next=target;
    const goto_programt::instructiont next_instr=*++next;
    if (goto_program_instruction_typet::ASSIGN != next_instr.type) return true;
    return get_affected_variable(instr) != get_affected_variable(next_instr);
  }
  case goto_program_instruction_typet::ASSIGN:
  {
    const exprt &rhs=to_code_assign(instr.code).rhs();
    if (ID_side_effect != rhs.id()) return false;
    return ID_nondet == to_side_effect_expr(rhs).get_statement();
  }
  default:
    return false;
  }
}

namespace
{
const char NS_SEP[]="::";
}
bool is_global_const(const irep_idt &name, const typet &type)
{
  if (!type.get_bool(ID_C_constant)) return false;
  return std::string::npos == id2string(name).find(NS_SEP);
}

namespace
{
const char RETURN_VALUE_IDENTIFIER[]="#return_value";
}
bool is_danger_user_variable(const irep_idt &id, const typet &type)
{
  if (ID_code == type.id()) return false;
  const std::string &name=id2string(id);
  if (std::string::npos != name.find(DANGER_PREFIX)) return false;
  if (std::string::npos != name.find(RETURN_VALUE_IDENTIFIER)) return false;
  return std::string::npos == name.find(CPROVER_PREFIX);
}

goto_programt::targett fix_target_by_offset(
    const goto_programt::const_targett &original_offset,
    goto_programt::targett new_offset,
    const goto_programt::const_targett &target)
{
  const size_t distance=std::distance(original_offset, target);
  std::advance(new_offset, distance);
  return new_offset;
}
