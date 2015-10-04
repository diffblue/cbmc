#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>

#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/constant/add_constant.h>
#include <cegis/danger/constant/literals_constant_strategy.h>
#include <cegis/danger/constant/default_constant_strategy.h>

namespace
{
const char NONDET_PREFIX[]="DANGER_CONSTANT_NONDET_";
}

size_t default_constant_strategy(danger_programt &program,
    const size_t max_length)
{
  const typet type(danger_meta_type());
  const bv_spect spec(type);
  add_danger_constant(program, from_integer(spec.max_value().to_ulong(), type));
  add_danger_constant(program, from_integer(0u, type));
  return 2u + literals_constant_strategy(program, max_length);
  /*for (size_t i=0; i < max_length; ++i)
  {
    const side_effect_expr_nondett value(type);
    std::string name(NONDET_PREFIX);
    add_danger_constant(program, name+=integer2string(i), value);
  }
  return 2u + max_length + literals_constant_strategy(program, max_length);*/
}
