/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BOOLBV_WIDTH_H
#define CPROVER_SOLVERS_FLATTENING_BOOLBV_WIDTH_H

#include <util/std_types.h>

class namespacet;

class boolbv_widtht
{
public:
  explicit boolbv_widtht(const namespacet &_ns);
  ~boolbv_widtht();

  std::size_t operator()(const typet &type) const
  {
    return get_entry(type).total_width;
  }

  struct membert
  {
    std::size_t offset, width;
  };

  const membert &get_member(
    const struct_typet &type,
    const irep_idt &member) const;

  std::size_t get_object_width(const pointer_typet &type) const;
  std::size_t get_offset_width(const pointer_typet &type) const;
  std::size_t get_address_width(const pointer_typet &type) const;

protected:
  const namespacet &ns;

  struct entryt
  {
    std::size_t total_width;
    std::vector<membert> members;
  };

  typedef std::unordered_map<typet, entryt, irep_hash> cachet;

  // the 'mutable' is allow const methods above
  mutable cachet cache;

  const entryt &get_entry(const typet &type) const;
};

#endif // CPROVER_SOLVERS_FLATTENING_BOOLBV_WIDTH_H
