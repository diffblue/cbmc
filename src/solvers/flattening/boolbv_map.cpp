/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv_map.h"

#include <util/threeval.h>

#include <solvers/prop/prop.h>

#ifdef DEBUG
#include <iostream>
#endif

std::string boolbv_mapt::map_entryt::get_value(const propt &prop) const
{
  std::string result;

  result.reserve(literal_map.size());

  for(const auto &literal : literal_map)
  {
    const tvt value = prop.l_get(literal);

    result += (value.is_true() ? '1' : (value.is_false() ? '0' : '?'));
  }

  return result;
}

void boolbv_mapt::show(std::ostream &out) const
{
  for(const auto &pair : mapping)
    out << pair.first << "=" << pair.second.get_value(prop) << '\n';
}

const bvt &boolbv_mapt::get_literals(
  const irep_idt &identifier,
  const typet &type,
  std::size_t width)
{
  std::pair<mappingt::iterator, bool> result=
    mapping.insert(std::pair<irep_idt, map_entryt>(
      identifier, map_entryt()));

  map_entryt &map_entry=result.first->second;

  if(result.second)
  { // actually inserted
    map_entry.type=type;
    map_entry.literal_map.reserve(width);

    for(std::size_t bit = 0; bit < width; ++bit)
    {
      map_entry.literal_map.push_back(prop.new_variable());

#ifdef DEBUG
      std::cout << "NEW: " << identifier << ":" << bit << "="
                << map_entry.literal_map.back() << '\n';
#endif
    }
  }

  INVARIANT(
    map_entry.literal_map.size() == width,
    "number of literals in the literal map shall equal the bitvector width");

  return map_entry.literal_map;
}

void boolbv_mapt::set_literals(
  const irep_idt &identifier,
  const typet &type,
  const bvt &literals)
{
  std::pair<mappingt::iterator, bool> result =
    mapping.insert(std::pair<irep_idt, map_entryt>(identifier, map_entryt()));

  map_entryt &map_entry = result.first->second;

  if(result.second)
  { // actually inserted
    map_entry.type = type;

    for(const auto &literal : literals)
    {
      INVARIANT(
        literal.is_constant() || literal.var_no() < prop.no_variables(),
        "variable number of non-constant literals shall be within bounds");
    }

    map_entry.literal_map = literals;
  }
  else
  {
    for(auto it = literals.begin(); it != literals.end(); ++it)
    {
      const literalt &literal = *it;

      INVARIANT(
        literal.is_constant() || literal.var_no() < prop.no_variables(),
        "variable number of non-constant literals shall be within bounds");

      const std::size_t bit = it - literals.begin();

      INVARIANT(
        bit < map_entry.literal_map.size(), "bit index shall be within bounds");

      prop.set_equal(map_entry.literal_map[bit], literal);
    }
  }
}

void boolbv_mapt::erase_literals(
  const irep_idt &identifier,
  const typet &)
{
  mapping.erase(identifier);
}
