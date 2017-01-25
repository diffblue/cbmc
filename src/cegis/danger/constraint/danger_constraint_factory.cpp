/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>
#include <util/options.h>

#include <cegis/danger/meta/meta_variable_names.h>
#include <cegis/invariant/meta/meta_variable_names.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/danger/constraint/danger_constraint_factory.h>

#define as_bool danger_component_as_bool

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

exprt create_danger_constraint(const size_t number_of_loops, const bool use_ranking)
{
  assert(number_of_loops >= 1 && "At least one loop required.");
  const constant_exprt min(get_min_value());
  and_exprt root;
  root.copy_to_operands(as_bool(get_Dx0()));
  for (size_t i=0; i < number_of_loops; ++i)
  {
    const notequal_exprt D0_x(as_bool(get_Dx(i)));
    const notequal_exprt D0_x_prime(as_bool(get_Dx_prime(i)));
    const notequal_exprt G0_x(as_bool(get_Gx(i)));
    const symbol_exprt R0_x(as_var(get_Rx(i, 0u))); // XXX: Lexicographical ranking?
    const symbol_exprt R0_x_prime(as_var(get_Rx_prime(i, 0u))); // XXX: Lexicographical ranking?
    const and_exprt D0_x_and_G0_x(D0_x, G0_x);
    const not_exprt not_D0_x_and_G0_x(D0_x_and_G0_x);
    exprt first_conseq;
    if (use_ranking)
    {
      const binary_predicate_exprt R0_x_gt_min(R0_x, ID_gt, min);
      const binary_predicate_exprt R0_x_prime_lt_R0_x(R0_x_prime, ID_lt, R0_x);
      first_conseq=and_exprt(R0_x_gt_min, D0_x_prime, R0_x_prime_lt_R0_x);
    } else first_conseq=D0_x_prime;
    const or_exprt first_implication(not_D0_x_and_G0_x, first_conseq);
    root.copy_to_operands(first_implication);
    const and_exprt D0_x_and_not_G0_x(D0_x, not_exprt(G0_x));
    const not_exprt not_D0_x_and_not_G0_x(D0_x_and_not_G0_x);
    const notequal_exprt D1_x(as_bool(get_Dx(i + 1)));
    const notequal_exprt A_x(as_bool(get_Ax()));
    exprt second_conseq;
    const bool is_last_component=(i == (number_of_loops - 1));
    if (is_last_component) second_conseq=not_exprt(A_x);
    else second_conseq=D1_x;
    const or_exprt second_implication(not_D0_x_and_not_G0_x, second_conseq);
    root.copy_to_operands(second_implication);
  }
  return root;
}
}

notequal_exprt danger_component_as_bool(const std::string &base_name)
{
  const constant_exprt rhs(from_integer(0u, cegis_default_integer_type()));
  return notequal_exprt(as_var(base_name), rhs);
}

danger_constraint::danger_constraint(const bool use_ranking) :
    use_ranking(use_ranking)
{
}

exprt danger_constraint::operator ()(const size_t number_of_loops) const
{
  return create_danger_constraint(number_of_loops, use_ranking);
}
