/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>

#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/safety/meta/meta_variable_names.h>
#include <cegis/safety/constraint/safety_constraint_factory.h>

namespace
{
symbol_exprt as_var(const std::string &base_name)
{
  const std::string name=get_cegis_meta_name(base_name);
  return symbol_exprt(name, cegis_default_integer_type());
}

constant_exprt get_min_value()
{
  const typet type(cegis_default_integer_type());
  const bv_spect spec(type);
  return from_integer(spec.min_value(), type);
}

notequal_exprt as_bool(const std::string &base_name)
{
  const constant_exprt rhs(from_integer(0u, cegis_default_integer_type()));
  return notequal_exprt(as_var(base_name), rhs);
}
}

exprt create_safety_constraint(const size_t number_of_loops)
{
  assert(number_of_loops >= 1 && "At least one loop required.");
  const constant_exprt min(get_min_value());
  const notequal_exprt A_x(as_bool(get_Ax()));
  and_exprt root;
  root.copy_to_operands(as_bool(get_Ix0()));
  for(size_t i=0; i < number_of_loops; ++i)
  {
    const notequal_exprt S0_x(as_bool(get_Ix(i)));
    const notequal_exprt G0_x(as_bool(get_Gx(i)));
    const and_exprt S0_x_and_G0_0x(S0_x, G0_x);
    const not_exprt not_S0_x_and_G0_0x(S0_x_and_G0_0x);
    const notequal_exprt S0_x_prime(as_bool(get_Ix_prime(i)));
    const or_exprt induction(not_S0_x_and_G0_0x, S0_x_prime);
    root.copy_to_operands(induction);
    const bool is_last_component=(i == (number_of_loops - 1));
    const not_exprt not_G0_x(G0_x);
    const and_exprt S0_x_and_not_G0_x(S0_x, not_G0_x);
    const not_exprt not_S0_x_and_not_G0_x(S0_x_and_not_G0_x);
    const notequal_exprt S1_x(as_bool(get_Ix(i + 1)));
    const exprt &conseq=is_last_component ? A_x : S1_x;
    const or_exprt implication(not_S0_x_and_not_G0_x, conseq);
    root.copy_to_operands(implication);
  }
  return root;
}
