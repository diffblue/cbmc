/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H
#define CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H

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

  struct map_bitt
  {
    map_bitt():is_set(false) { }
    bool is_set;
    literalt l;
  };

  typedef std::vector<map_bitt> literal_mapt;

  class map_entryt
  {
  public:
    map_entryt():width(0), bvtype(bvtypet::IS_UNKNOWN)
    {
    }

    std::size_t width;
    bvtypet bvtype;
    typet type;
    literal_mapt literal_map;

    std::string get_value(const propt &) const;
  };

  typedef std::unordered_map<irep_idt, map_entryt> mappingt;
  mappingt mapping;

  void show() const;

  map_entryt &get_map_entry(
    const irep_idt &identifier,
    const typet &type);

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

protected:
  propt &prop;
  const boolbv_widtht &boolbv_width;
};

#endif // CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H
