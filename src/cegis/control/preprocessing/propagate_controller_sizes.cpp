/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <deque>
#include <algorithm>

#include <goto-programs/goto_functions.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/control/value/control_vars.h>

namespace
{
template<class struct_exprt_typet, class exprt_typet>
exprt_typet &get_comp(const namespacet &ns, struct_exprt_typet &value,
    const char * const comp)
{
  const struct_typet &type=to_struct_type(ns.follow(value.type()));
  const struct_typet::componentst &comps=type.components();
  for (size_t i=0; i < comps.size(); ++i)
    if (id2string(comps[i].get_name()) == comp) return value.operands()[i];
  assert(!"Solution component not found.");
}
}

const exprt &get_controller_comp(const namespacet &ns,
    const struct_exprt &value, const char * const comp)
{
  return get_comp<const struct_exprt, const exprt>(ns, value, comp);
}

exprt &get_controller_comp(const namespacet &ns, struct_exprt &value,
    const char * const comp)
{
  return get_comp<struct_exprt, exprt>(ns, value, comp);
}

const array_exprt &get_a_controller_comp(const namespacet &ns,
    const struct_exprt &value)
{
  return to_array_expr(
      get_controller_comp(ns, value, CEGIS_CONTROL_A_MEMBER_NAME));
}

const array_exprt &get_b_controller_comp(const namespacet &ns,
    const struct_exprt &value)
{
  return to_array_expr(
      get_controller_comp(ns, value, CEGIS_CONTROL_B_MEMBER_NAME));
}

namespace
{
const exprt &get_a_size(const namespacet &ns, const struct_exprt &value)
{
  return get_controller_comp(ns, value, CEGIS_CONTROL_A_SIZE_MEMBER_NAME);
}

const exprt &get_b_size(const namespacet &ns, const struct_exprt &value)
{
  return get_controller_comp(ns, value, CEGIS_CONTROL_B_SIZE_MEMBER_NAME);
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
}

void propagate_controller_sizes(const symbol_tablet &st, goto_functionst &gf)
{
  if (!st.has_symbol(CEGIS_CONTROL_SOLUTION_VAR_NAME)) return;
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

namespace
{
bool is_sol_assign(const goto_programt::instructiont &instr)
{
  if (goto_program_instruction_typet::ASSIGN != instr.type) return false;
  const std::string &var=id2string(get_affected_variable(instr));
  return CEGIS_CONTROL_SOLUTION_VAR_NAME == var;
}
}

goto_programt::targett get_solution_assignment(goto_programt &body)
{
  goto_programt::instructionst &i=body.instructions;
  const goto_programt::targett end(i.end());
  const goto_programt::targett pos=std::find_if(i.begin(), end, is_sol_assign);
  assert(end != pos);
  return pos;
}

void remove_solution_assignment(goto_programt &body)
{
  body.instructions.erase(get_solution_assignment(body));
}
