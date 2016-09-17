#include <deque>
#include <algorithm>

#include <cegis/control/value/control_vars.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/find_cprover_initialize.h>
#include <cegis/control/learn/nondet_solution.h>

namespace
{
bool is_sol_assign(const goto_programt::instructiont &instr)
{
  if (goto_program_instruction_typet::ASSIGN != instr.type) return false;
  const std::string &var=id2string(get_affected_variable(instr));
  return CEGIS_CONTROL_SOLUTION_VAR_NAME == var;
}

void remove_solution_assignment_from_cprover_init(goto_functionst &gf)
{
  goto_programt::instructionst &i=get_body(gf, CPROVER_INIT).instructions;
  const goto_programt::targett end(i.end());
  const goto_programt::targett pos=std::find_if(i.begin(), end, is_sol_assign);
  assert(end != pos);
  i.erase(pos);
}

const exprt &get_comp(const namespacet &ns, const struct_exprt &value,
    const char * const comp)
{
  const struct_typet &type=to_struct_type(ns.follow(value.type()));
  const struct_typet::componentst &comps=type.components();
  for (size_t i=0; i < comps.size(); ++i)
    if (id2string(comps[i].get_name()) == comp) return value.operands()[i];
  assert(!"Solution component not found.");
}

const exprt &get_a_size(const namespacet &ns, const struct_exprt &value)
{
  return get_comp(ns, value, CEGIS_CONTROL_A_SIZE_MEMBER_NAME);
}

const exprt &get_b_size(const namespacet &ns, const struct_exprt &value)
{
  return get_comp(ns, value, CEGIS_CONTROL_B_SIZE_MEMBER_NAME);
}

class replace_sizes_visitort: public expr_visitort
{
  std::deque<exprt *> a_sizes, b_sizes;
  const exprt &a_size;
  const exprt &b_size;
public:
  replace_sizes_visitort(const exprt &a_size, const exprt &b_size) :
      a_size(a_size), b_size(b_size)
  {
  }

  virtual ~replace_sizes_visitort()
  {
    for (exprt * const expr : a_sizes)
      *expr=a_size;
    for (exprt * const expr : b_sizes)
      *expr=b_size;
  }

  virtual void operator()(exprt &expr)
  {
    if (ID_member != expr.id()) return;
    const member_exprt &member=to_member_expr(expr);
    const exprt &struct_op=member.struct_op();
    if (ID_symbol != struct_op.id()) return;
    const symbol_exprt &symbol=to_symbol_expr(struct_op);
    const std::string &var=id2string(symbol.get_identifier());
    if (CEGIS_CONTROL_SOLUTION_VAR_NAME != var) return;
    const std::string &comp=id2string(member.get_component_name());
    if (CEGIS_CONTROL_A_SIZE_MEMBER_NAME == comp) a_sizes.push_back(&expr);
    else if (CEGIS_CONTROL_B_SIZE_MEMBER_NAME == comp) b_sizes.push_back(&expr);
  }
};

void replace_controller_sizes(const symbol_tablet &st, goto_functionst &gf)
{
  const symbolt &symbol=st.lookup(CEGIS_CONTROL_SOLUTION_VAR_NAME);
  const struct_exprt &controller_value=to_struct_expr(symbol.value);
  const namespacet ns(st);
  const exprt &a_size=get_a_size(ns, controller_value);
  const exprt &b_size=get_b_size(ns, controller_value);
  replace_sizes_visitort visitor(a_size, b_size);
  goto_programt &body=get_entry_body(gf);
  for (goto_programt::instructiont &instr : body.instructions)
  {
    instr.code.visit(visitor);
    instr.guard.visit(visitor);
  }
}
}

void nondet_control_solution(const symbol_tablet &st, goto_functionst &gf)
{
  const std::string name(CEGIS_CONTROL_SOLUTION_VAR_NAME);
  const symbolt &symbol=st.lookup(name);
  replace_controller_sizes(st, gf);
  const side_effect_expr_nondett value(symbol.type);
  const symbol_exprt solution_var(symbol.symbol_expr());
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett pos(find_cprover_initialize(body));
  pos=cegis_assign_user_variable(st, gf, std::prev(pos), name, value);
  remove_solution_assignment_from_cprover_init(gf);
}
