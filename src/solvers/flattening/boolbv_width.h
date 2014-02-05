/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOOLBV_WIDTH_H
#define CPROVER_BOOLBV_WIDTH_H

#include <util/std_types.h>
#include <util/namespace.h>
#include <util/hash_cont.h>

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

protected:
  const namespacet &ns;

  struct entryt
  {
    std::size_t total_width;
    std::vector<membert> members;
  };
  
  typedef hash_map_cont<typet, entryt, irep_hash> cachet;

  // the pointer is allow const methods above
  cachet *cache;

  const entryt &get_entry(const typet &type) const;
};

#if 0
bool boolbv_member_offset(
  const struct_typet &type,
  const irep_idt &member,
  std::size_t &offset,
  const namespacet &ns);

bool boolbv_get_width(
  const typet &type,
  std::size_t &width,
  const namespacet &ns);
#endif

#endif
