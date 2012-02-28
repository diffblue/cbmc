/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv_map.h"
#include "boolbv_width.h"

//#define DEBUG

/*******************************************************************\

Function: boolbv_mapt::get_map_entry

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

boolbv_mapt::map_entryt &boolbv_mapt::get_map_entry(
  const irep_idt &identifier,
  const typet &type)
{
  if(type.id()==ID_symbol)
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

  assert(map_entry.literal_map.size()==map_entry.width);

  return map_entry;
}

/*******************************************************************\

Function: boolbv_mapt::show

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbv_mapt::show() const
{
  for(mappingt::const_iterator it=mapping.begin();
      it!=mapping.end();
      it++)
  {
  }
}

/*******************************************************************\

Function: boolbv_mapt::get_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt boolbv_mapt::get_literal(
  const irep_idt &identifier,
  const unsigned bit,
  const typet &type)
{
  map_entryt &map_entry=get_map_entry(identifier, type);

  assert(bit<map_entry.literal_map.size());
  map_bitt &mb=map_entry.literal_map[bit];

  if(mb.is_set)
    return mb.l;

  literalt l=prop.new_variable();

  mb.is_set=true;
  mb.l=l;

  #ifdef DEBUG
  std::cout << "NEW: " << identifier << ":" << bit
            << "=" << l << std::endl;
  #endif

  return l;
}

/*******************************************************************\

Function: boolbv_mapt::set_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void boolbv_mapt::set_literal(
  const irep_idt &identifier,
  const unsigned bit,
  const typet &type,
  literalt literal)
{
  assert(literal.is_constant() ||
         literal.var_no()<prop.no_variables());

  map_entryt &map_entry=get_map_entry(identifier, type);
  assert(bit<map_entry.literal_map.size());
  map_bitt &mb=map_entry.literal_map[bit];

  if(mb.is_set)
  {
    prop.set_equal(mb.l, literal);
    return;
  }

  mb.is_set=true;
  mb.l=literal;
}

