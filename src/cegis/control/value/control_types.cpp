#include <util/std_types.h>
#include <util/symbol_table.h>

#include <cegis/control/value/control_vars.h>
#include <cegis/control/value/control_types.h>

const symbol_typet &control_solution_type(const symbol_tablet &st)
{
  return to_symbol_type(st.lookup(CEGIS_CONTROL_SOLUTION_VAR_NAME).type);
}

const array_typet &control_vector_solution_type(const symbol_tablet &st)
{
  return to_array_type(st.lookup(CEGIS_CONTROL_VECTOR_SOLUTION_VAR_NAME).type);
}

namespace
{
const struct_typet::componentt &get_comp(const symbol_tablet &st,
    const char * const name)
{
  const typet &type=st.lookup(control_solution_type(st).get_identifier()).type;
  return to_struct_type(type).get_component(name);
}
}

const typet &control_float_value_type(const symbol_tablet &st)
{
  const struct_typet::componentt &c=get_comp(st, CEGIS_CONTROL_A_MEMBER_NAME);
  return to_array_type(c.type()).subtype();
}

const typet &control_array_size_type(const symbol_tablet &st)
{
  const struct_typet::componentt &c=get_comp(st, CEGIS_CONTROL_A_MEMBER_NAME);
  return to_array_type(c.type()).size().type();
}

const typet &control_runtime_array_size_type(const symbol_tablet &st)
{
  const char * const name=CEGIS_CONTROL_A_SIZE_MEMBER_NAME;
  const struct_typet::componentt &c=get_comp(st, name);
  return c.type();
}
