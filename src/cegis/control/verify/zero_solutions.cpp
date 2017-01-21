#include <linking/zero_initializer.h>

#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/control/value/control_solution.h>
#include <cegis/control/value/control_vector_solution.h>
#include <cegis/control/value/control_types.h>
#include <cegis/control/value/control_vars.h>
#include <cegis/control/preprocessing/propagate_controller_sizes.h>
#include <cegis/control/verify/zero_solutions.h>

bool is_vector_solution_config(const symbol_tablet &st)
{
  return st.has_symbol(CEGIS_CONTROL_VECTOR_SOLUTION_VAR_NAME);
}

zero_rational_solutiont::zero_rational_solutiont(const symbol_tablet &st) :
    st(st)
{
}

namespace
{
struct_exprt make_zero(const namespacet &ns, const symbol_typet &type)
{
  const source_locationt loc(default_cegis_source_location());
  null_message_handlert msg;
  return to_struct_expr(zero_initializer(type, loc, ns, msg));
}
}

void zero_rational_solutiont::operator ()(control_solutiont &solution) const
{
  if (!solution.a.operands().empty()) return;
  const symbol_typet &type=control_solution_type(st);
  const namespacet ns(st);
  const struct_exprt zero_struct=make_zero(ns, type);
  solution.a=get_a_controller_comp(ns, zero_struct);
  solution.b=get_b_controller_comp(ns, zero_struct);
}

zero_vector_solutiont::zero_vector_solutiont(const symbol_tablet &st) :
    st(st)
{
}

void zero_vector_solutiont::operator ()(
    control_vector_solutiont &solution) const
{
  if (!solution.K.operands().empty()) return;
  const namespacet ns(st);
  const array_typet &type=control_vector_solution_type(st);
  const source_locationt loc(default_cegis_source_location());
  null_message_handlert msg;
  solution.K=to_array_expr(zero_initializer(type, loc, ns, msg));
}
