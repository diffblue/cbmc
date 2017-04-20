/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>

#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/constant/add_constant.h>
#include <cegis/invariant/constant/literals_constant_strategy.h>
#include <cegis/invariant/constant/default_constant_strategy.h>

size_t default_constant_strategy(invariant_programt &program,
    const size_t max_length)
{
  const typet type(cegis_default_integer_type());
  const bv_spect spec(type);
  add_danger_constant(program, from_integer(spec.max_value().to_ulong(), type));
  add_danger_constant(program, from_integer(0u, type));
  return std::max(size_t(1u), literals_constant_strategy(program, max_length));
  // return 2u + literals_constant_strategy(program, max_length);
  /*for (size_t i=0; i < max_length; ++i)
   {
   const side_effect_expr_nondett value(type);
   std::string name(NONDET_PREFIX);
   add_danger_constant(program, name+=integer2string(i), value);
   }
   return 2u + max_length + literals_constant_strategy(program, max_length);*/
}
