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
  std::string result;

  result.reserve(literal_map.size());

  for(std::size_t i=0; i<literal_map.size(); i++)
  {
    char ch='*';

    if(literal_map[i].is_set)
    {
      tvt value=prop.l_get(literal_map[i].l);

      if(value.is_true())
        ch='1';
      else if(value.is_false())
        ch='0';
      else
        ch='?';
    }

    result=result+ch;
  }

  return result;
}

boolbv_mapt::map_entryt &boolbv_mapt::get_map_entry(
  const irep_idt &identifier,
  const typet &type)
{
  if(type.id() == ID_symbol_type)
    return get_map_entry(identifier, ns.follow(type));

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

  Forall_literals(it, literals)
  {
    literalt &l=*it;
    const std::size_t bit=it-literals.begin();

    INVARIANT(
      bit < map_entry.literal_map.size(), "bit index shall be within bounds");
    map_bitt &mb=map_entry.literal_map[bit];

    if(mb.is_set)
    {
      l=mb.l;
      continue;
    }

    l=prop.new_variable();

    mb.is_set=true;
    mb.l=l;

    #ifdef DEBUG
    std::cout << "NEW: " << identifier << ":" << bit
              << "=" << l << '\n';
    #endif
  }
}

void boolbv_mapt::set_literals(
  const irep_idt &identifier,
  const typet &type,
  const bvt &literals)
{
  map_entryt &map_entry=get_map_entry(identifier, type);

  forall_literals(it, literals)
  {
    const literalt &literal=*it;

    INVARIANT(
      literal.is_constant() || literal.var_no() < prop.no_variables(),
      "variable number of non-constant literals shall be within bounds");

    const std::size_t bit = it - literals.begin();

    INVARIANT(
      bit < map_entry.literal_map.size(), "bit index shall be within bounds");
    map_bitt &mb=map_entry.literal_map[bit];

    if(mb.is_set)
    {
      prop.set_equal(mb.l, literal);
      continue;
    }

    mb.is_set=true;
    mb.l=literal;
  }
}

void boolbv_mapt::erase_literals(
  const irep_idt &identifier,
  const typet &)
{
  mapping.erase(identifier);
}
