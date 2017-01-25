/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <util/arith_tools.h>

#include <cegis/constant/literals_collector.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/jsa/value/jsa_types.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>
#include <cegis/jsa/preprocessing/default_jsa_constant_strategy.h>

namespace
{
std::string get_name(size_t index)
{
  std::string name(JSA_CONSTANT_PREFIX);
  return name+=integer2string(index);
}
}

goto_programt::targett default_jsa_constant_strategy(symbol_tablet &st,
    goto_functionst &gf)
{
  const std::vector<constant_exprt> literals(collect_integer_literals(st, gf));
  const typet word_type(jsa_word_type());
  size_t const_index=0u;
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett pos=body.instructions.begin();
  for (const constant_exprt &expr : literals)
  {
    mp_integer value;
    to_integer(expr, value);
    const constant_exprt expr_value(from_integer(value, word_type));
    const std::string base_name(get_name(const_index++));
    pos=body.insert_after(pos);
    declare_jsa_meta_variable(st, pos, base_name, expr_value.type());
    pos=assign_jsa_meta_variable(st, gf, pos, base_name, expr_value);
  }
  return pos;
}
