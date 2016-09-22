#include <util/ieee_float.h>
#include <util/fixedbv.h>
#include <util/arith_tools.h>
#include <util/message.h>
#include <ansi-c/c_types.h>
#include <linking/zero_initializer.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/find_cprover_initialize.h>

#include <cegis/control/value/float_helper.h>
#include <cegis/control/value/control_vars.h>
#include <cegis/control/value/control_types.h>
#include <cegis/control/value/control_solution.h>
#include <cegis/control/options/control_program.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/verify/insert_solution.h>

namespace
{
void set_array_data(array_exprt &array, const symbol_tablet &st,
    const std::vector<double> &data)
{
  array_exprt::operandst &ops=array.operands();
  assert(data.size() <= ops.size());
  for (size_t i=0; i < data.size(); ++i)
    ops[i]=to_control_float_expr(st, data[i]);
}

exprt &get_comp(struct_exprt::operandst &ops, const struct_typet &struct_type,
    const char * const comp)
{
  const struct_typet::componentst &comps=struct_type.components();
  const size_t comps_size=comps.size();
  size_t offset=0;
  for (offset=0; offset < comps_size; ++offset)
    if (id2string(comps[offset].get_name()) == comp) break;
  assert(offset < comps_size);
  return ops[offset];
}

void set_array(struct_exprt::operandst &ops, const symbol_tablet &st,
    const struct_typet &struct_type, const std::vector<double> &array,
    const char * const comp)
{
  set_array_data(to_array_expr(get_comp(ops, struct_type, comp)), st, array);
  const typet &size_type=control_runtime_array_size_type(st);
  const constant_exprt size(from_integer(array.size(), size_type));
  const char * const sz_comp=
  CEGIS_CONTROL_A_MEMBER_NAME ?
  CEGIS_CONTROL_A_SIZE_MEMBER_NAME :
                                CEGIS_CONTROL_B_SIZE_MEMBER_NAME;
  exprt &sz=get_comp(ops, struct_type, sz_comp);
  sz=size;
}

struct_exprt to_struct_expr(const symbol_tablet &st,
    const control_solutiont &solution, const source_locationt &loc)
{
  const symbol_typet &type=control_solution_type(st);
  const namespacet ns(st);
  const struct_typet &struct_type=to_struct_type(ns.follow(type));
  null_message_handlert msg;
  const exprt zero(zero_initializer(type, loc, ns, msg));
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
  goto_functionst &gf=program.gf;
  goto_programt &init=get_body(gf, CPROVER_INIT);
  const goto_programt::targett pos=get_solution_assignment(init);
  const symbol_tablet &st=program.st;
  const source_locationt &loc=pos->source_location;
  const struct_exprt value(to_struct_expr(st, solution, loc));
  to_code_assign(pos->code).rhs()=value;
}
