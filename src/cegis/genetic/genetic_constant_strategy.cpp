/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>
#include <util/mp_arith.h>

#include <cegis/cegis-util/constant_width.h>

#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/literals.h>
#include <cegis/invariant/constant/literals_constant_strategy.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/genetic/genetic_constant_strategy.h>

namespace
{
std::string get_name(size_t index)
{
  std::string name(CEGIS_CONSTANT_PREFIX);
  return name+=integer2string(index);
}

// XXX: Debug
bool constants_printed=false;
// XXX: Debug
}

// XXX: Debug
#include <iostream>
// XXX: Debug

size_t genetic_constant_strategy(invariant_programt &prog,
    const size_t max_length)
{
  symbol_tablet &st=prog.st;
  const namespacet ns(st);
  goto_functionst &gf=prog.gf;
  goto_programt::targett pos=prog.invariant_range.begin;
  const std::vector<constant_exprt> literals(collect_literal_constants(prog));
  size_t max_word_width=0u;
  size_t const_index=0u;
  // XXX: Literals strategy, benchmark performance
  for(const constant_exprt &expr : literals)
  {
    // XXX: Debug
    if(!constants_printed)
    {
      std::cout << "<id>" << const_index << "</id>" << std::endl;
      std::cout << "<value>" << from_expr(ns, "", expr) << "</value>\n";
    }
    // XXX: Debug
    const std::string base_name(get_name(const_index++));
    pos=declare_cegis_meta_variable(st, gf, pos, base_name, expr.type());
    pos=assign_cegis_meta_variable(st, gf, pos, base_name, expr);
    max_word_width=std::max(max_word_width, get_min_word_width(expr));
  }
  constants_printed=true;

  // XXX: 0/1 constant strategy, benchmark performance
  /*const typet type(danger_meta_type());
   const bv_spect spec(type);
   const std::vector<constant_exprt> def={ from_integer(0u, type), from_integer(
   1u, type), from_integer(spec.max_value().to_ulong(), type) };*/
  /*const std::vector<constant_exprt> def={ from_integer(0u, type), from_integer(
   1u, type) };*/
  /*for (const constant_exprt &expr : def)
   {
   // XXX: Debug
   std::cout << "<id>" << const_index << "</id>" << std::endl;
   std::cout << "<value>" << expr.to_string() << "</value>" << std::endl;
   // XXX: Debug
   const std::string base_name(get_name(const_index++));
   pos=declare_danger_variable(st, gf, pos, base_name, expr.type());
   pos=assign_danger_variable(st, gf, pos, base_name, expr);
   max_word_width=std::max(max_word_width, get_min_word_width(expr));
   }*/
  return max_word_width;
  /*typet type=danger_meta_type(); // XXX: Currently single data type
   type.set(ID_C_constant, true);
   // TODO: Multiply by number of programs and loops?
   for (size_t i=0; i < max_length; ++i)
   pos=declare_danger_variable(st, gf, pos, get_ndt_name(const_index++), type);*/
}
