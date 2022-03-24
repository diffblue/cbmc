/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H
#define CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H

#include <util/type.h>

#include <solvers/prop/literal.h>

#include <functional>
#include <iosfwd>

class propt;

class boolbv_mapt
{
public:
  explicit boolbv_mapt(propt &_prop) : prop(_prop)
  {
  }

  class map_entryt
  {
  public:
    typet type;
    bvt literal_map;

    std::string get_value(const propt &) const;
  };

  typedef std::unordered_map<irep_idt, map_entryt> mappingt;

  void show(std::ostream &out) const;

  const bvt &get_literals(
    const irep_idt &identifier,
    const typet &type,
    std::size_t width);

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
};

#endif // CPROVER_SOLVERS_FLATTENING_BOOLBV_MAP_H
