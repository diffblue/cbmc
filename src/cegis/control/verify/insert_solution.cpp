#include <util/ieee_float.h>
#include <util/arith_tools.h>
#include <util/message.h>
#include <ansi-c/c_types.h>
#include <linking/zero_initializer.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/find_cprover_initialize.h>

#include <cegis/control/value/control_vars.h>
#include <cegis/control/value/control_types.h>
#include <cegis/control/value/control_solution.h>
#include <cegis/control/options/control_program.h>
#include <cegis/control/verify/insert_solution.h>

namespace
{
constant_exprt to_double_expr(const symbol_tablet &st, const double value)
{
  const typet &data_type=control_float_value_type(st);
  const ieee_float_spect spec(to_floatbv_type(data_type));
  ieee_floatt ieee(spec);
  ieee.from_double(value);
  return ieee.to_expr();
}

void set_array_data(array_exprt &array, const symbol_tablet &st,
    const std::vector<double> &data)
{
  array_exprt::operandst &ops=array.operands();
  assert(data.size() <= ops.size());
  for (size_t i=0; i < data.size(); ++i)
    ops[i]=to_double_expr(st, data[i]);
}

void set_array(struct_exprt::operandst &ops, const symbol_tablet &st,
    const struct_typet &struct_type, const std::vector<double> &array,
    size_t offset=0)
{
  const struct_typet::componentst &comps=struct_type.components();
  while (comps[offset].get_is_padding())
    ++offset;
  set_array_data(to_array_expr(ops[offset]), st, array);
  const typet &size_type=control_runtime_array_size_type(st);
  const constant_exprt size(from_integer(array.size(), size_type));
  ops[++offset]=size;
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
  set_array(ops, st, struct_type, solution.a);
  set_array(ops, st, struct_type, solution.b, 2);
  return result;
}
}

void insert_solution(control_programt &program,
    const control_solutiont &solution)
{
  goto_functionst &gf=program.gf;
  goto_programt &body=get_entry_body(gf);
  const goto_programt::targett pos=find_cprover_initialize(body);
  const irep_idt name(CEGIS_CONTROL_SOLUTION_VAR_NAME);
  const symbol_tablet &st=program.st;
  const source_locationt &loc=pos->source_location;
  const struct_exprt value(to_struct_expr(st, solution, loc));
  cegis_assign_user_variable(st, gf, pos, name, value);
}
