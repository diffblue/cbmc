/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/cegis-util/constant_width.h>
#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/constant/literals_collector.h>

namespace
{
std::string get_name(size_t index)
{
  std::string name(CEGIS_CONSTANT_PREFIX);
  return name+=integer2string(index);
}
}

size_t default_cegis_constant_strategy(symbol_tablet &st, goto_functionst &gf)
{
  const std::vector<constant_exprt> literals(collect_integer_literals(st, gf));
  size_t max_word_width=0u;
  size_t const_index=0u;
  goto_programt::targett pos=get_entry_body(gf).instructions.begin();
  // XXX: Literals strategy, benchmark performance
  for(const constant_exprt &expr : literals)
  {
    // XXX: Debug
    // std::cout << "<id>" << const_index << "</id>" << std::endl;
    // std::cout << "<value>" << expr.to_string() << "</value>" << std::endl;
    // XXX: Debug
    const std::string base_name(get_name(const_index++));
    pos=declare_cegis_meta_variable(st, gf, pos, base_name, expr.type());
    pos=assign_cegis_meta_variable(st, gf, pos, base_name, expr);
    max_word_width=std::max(max_word_width, get_min_word_width(expr));
  }
  return max_word_width;
}
