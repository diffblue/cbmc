/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>
#include <linking/zero_initializer.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>

#include <cegis/control/value/control_vars.h>
#include <cegis/control/value/control_types.h>
#include <cegis/control/value/control_solution.h>
#include <cegis/control/value/control_vector_solution.h>
#include <cegis/control/options/control_program.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>

namespace
{
exprt &get_comp(struct_exprt::operandst &ops, const struct_typet &struct_type,
    const char * const comp)
{
  const struct_typet::componentst &comps=struct_type.components();
  const size_t comps_size=comps.size();
  size_t offset=0;
  for(offset=0; offset < comps_size; ++offset)
    if(id2string(comps[offset].get_name()) == comp) break;
  assert(offset < comps_size);
  return ops[offset];
}

void set_array(struct_exprt::operandst &ops, const symbol_tablet &st,
    const struct_typet &struct_type, const array_exprt &array,
    const char * const comp)
{
  to_array_expr(get_comp(ops, struct_type, comp))=array;
  const typet &size_type=control_runtime_array_size_type(st);
  const constant_exprt size(from_integer(array.operands().size(), size_type));
  const char * const sz_comp=
      std::string(CEGIS_CONTROL_A_MEMBER_NAME) == comp ?
          CEGIS_CONTROL_A_SIZE_MEMBER_NAME : CEGIS_CONTROL_B_SIZE_MEMBER_NAME;
  get_comp(ops, struct_type, sz_comp)=size;
}

struct_exprt to_struct_expr(const symbol_tablet &st,
    const control_solutiont &solution, const source_locationt &loc)
{
  const symbol_typet &type=control_solution_type(st);
  const namespacet ns(st);
  const struct_typet &struct_type=to_struct_type(ns.follow(type));
  const exprt zero(zero_initializer(type, loc, ns));
  struct_exprt result(to_struct_expr(zero));
  struct_exprt::operandst &ops=result.operands();
  set_array(ops, st, struct_type, solution.a, CEGIS_CONTROL_A_MEMBER_NAME);
  set_array(ops, st, struct_type, solution.b, CEGIS_CONTROL_B_MEMBER_NAME);
  return result;
}
}

void insert_solution(control_programt &program,
    const control_solutiont &solution)
{
  goto_programt &init=get_body(program.gf, CPROVER_INIT);
  const goto_programt::targett pos=get_solution_assignment(init);
  const symbol_tablet &st=program.st;
  const source_locationt &loc=pos->source_location;
  to_code_assign(pos->code).rhs()=to_struct_expr(st, solution, loc);
}

namespace
{
class is_assignment_tot
{
  const std::string name;
public:
  explicit is_assignment_tot(const std::string &name):name(name)
  {
  }

  bool operator()(const goto_programt::instructiont &instr) const
  {
    if(goto_program_instruction_typet::ASSIGN != instr.type) return false;
    const std::string &var=id2string(get_affected_variable(instr));
    return name == var;
  }
};
}

void insert_solution(control_programt &program,
    const control_vector_solutiont &solution)
{
  goto_programt &init=get_body(program.gf, CPROVER_INIT);
  goto_programt::instructionst &instrs=init.instructions;
  const goto_programt::targett end(instrs.end());
  const is_assignment_tot pred(CEGIS_CONTROL_VECTOR_SOLUTION_VAR_NAME);
  const goto_programt::targett it=std::find_if(instrs.begin(), end, pred);
  assert(end != it);
  to_code_assign(it->code).rhs()=solution.K;
}
