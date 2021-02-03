/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H
#define CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H

#include <iosfwd>
#include <vector>

#include <util/type.h>
#include <util/namespace.h>

#include <solvers/prop/prop.h>

#include "boolbv_type.h"
#include "boolbv_width.h"

class boolbv_mapt
{
public:
  boolbv_mapt(propt &_prop, const boolbv_widtht &_boolbv_width)
    : prop(_prop), boolbv_width(_boolbv_width)
  {
  }

  class map_entryt
  {
  public:
    map_entryt():width(0), bvtype(bvtypet::IS_UNKNOWN)
    {
    }

    std::size_t width;
    bvtypet bvtype;
    typet type;
    bvt literal_map;

    std::string get_value(const propt &) const;
  };

  typedef std::unordered_map<irep_idt, map_entryt> mappingt;

  void show(std::ostream &out) const;

  void get_literals(
    const irep_idt &identifier,
    const typet &type,
    const std::size_t width,
    bvt &literals);

  void set_literals(
    const irep_idt &identifier,
    const typet &type,
    const bvt &literals);

  void erase_literals(
    const irep_idt &identifier,
    const typet &type);

  optionalt<std::reference_wrapper<const map_entryt>>
  get_map_entry(const irep_idt &identifier) const
  {
    const auto entry = mapping.find(identifier);
    if(entry == mapping.end())
      return {};

    return optionalt<std::reference_wrapper<const map_entryt>>(entry->second);
  }

  const mappingt &get_mapping() const
  {
    return mapping;
  }

protected:
  mappingt mapping;
  propt &prop;
  const boolbv_widtht &boolbv_width;
};

#endif // CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H
