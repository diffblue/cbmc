/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv_map.h"

#include <util/threeval.h>

#include <solvers/prop/prop.h>

#include "boolbv_width.h"

#ifdef DEBUG
#include <iostream>
#endif

std::string boolbv_mapt::map_entryt::get_value(const propt &prop) const
{
  if(!is_set)
    return std::string(literal_map.size(), '*');

  std::string result;

  result.reserve(literal_map.size());

  for(const auto &literal : literal_map)
  {
    const tvt value = prop.l_get(literal);

    result += (value.is_true() ? '1' : (value.is_false() ? '0' : '?'));
  }

  return result;
}

boolbv_mapt::map_entryt &boolbv_mapt::get_map_entry(
  const irep_idt &identifier,
  const typet &type)
{
  std::pair<mappingt::iterator, bool> result=
    mapping.insert(std::pair<irep_idt, map_entryt>(
      identifier, map_entryt()));

  map_entryt &map_entry=result.first->second;

  if(result.second)
  { // actually inserted
    map_entry.type=type;
    map_entry.width=boolbv_width(type);
    map_entry.bvtype=get_bvtype(type);
    map_entry.literal_map.resize(map_entry.width);
  }

  INVARIANT(
    map_entry.literal_map.size() == map_entry.width,
    "number of literals in the literal map shall equal the bitvector width");

  return map_entry;
}

void boolbv_mapt::show() const
{
  for(mappingt::const_iterator it=mapping.begin();
      it!=mapping.end();
      it++)
  {
  }
}

void boolbv_mapt::get_literals(
  const irep_idt &identifier,
  const typet &type,
  const std::size_t width,
  bvt &literals)
{
  map_entryt &map_entry=get_map_entry(identifier, type);

  PRECONDITION(literals.size() == width);
  INVARIANT(
    map_entry.literal_map.size() == width,
    "number of literals in the literal map shall equal the bitvector width");

  if(!map_entry.is_set)
  {
#ifdef DEBUG
    std::size_t bit = 0;
#endif
    for(auto &literal : map_entry.literal_map)
    {
      literal = prop.new_variable();

#ifdef DEBUG
      std::cout << "NEW: " << identifier << ":" << bit << "=" << literal
                << '\n';
      ++bit;
#endif
    }

    map_entry.is_set = true;
  }

  literals = map_entry.literal_map;
}

void boolbv_mapt::set_literals(
  const irep_idt &identifier,
  const typet &type,
  const bvt &literals)
{
  map_entryt &map_entry=get_map_entry(identifier, type);

  for(auto it = literals.begin(); it != literals.end(); ++it)
  {
    const literalt &literal=*it;

    INVARIANT(
      literal.is_constant() || literal.var_no() < prop.no_variables(),
      "variable number of non-constant literals shall be within bounds");

    const std::size_t bit = it - literals.begin();

    INVARIANT(
      bit < map_entry.literal_map.size(), "bit index shall be within bounds");

    if(map_entry.is_set)
    {
      prop.set_equal(map_entry.literal_map[bit], literal);
      continue;
    }

    map_entry.literal_map[bit] = literal;
  }

  map_entry.is_set = true;
}

void boolbv_mapt::erase_literals(
  const irep_idt &identifier,
  const typet &)
{
  mapping.erase(identifier);
}
