/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BOOLBV_WIDTH_H
#define CPROVER_SOLVERS_FLATTENING_BOOLBV_WIDTH_H

#include <util/type.h>

class namespacet;
class struct_typet;

class boolbv_widtht
{
public:
  explicit boolbv_widtht(const namespacet &_ns);
  virtual ~boolbv_widtht() = default;

  virtual std::size_t operator()(const typet &type) const
  {
    const auto &entry_opt = get_entry(type);
    CHECK_RETURN(entry_opt.has_value());
    return entry_opt->total_width;
  }

  virtual optionalt<std::size_t> get_width_opt(const typet &type) const
  {
    const auto &entry_opt = get_entry(type);
    if(!entry_opt.has_value())
      return {};
    return entry_opt->total_width;
  }

  struct membert
  {
    std::size_t offset, width;
  };

  const membert &
  get_member(const struct_typet &type, const irep_idt &member) const;

protected:
  const namespacet &ns;

  struct defined_entryt
  {
    explicit defined_entryt(std::size_t total_width) : total_width(total_width)
    {
    }

    std::size_t total_width;
    std::vector<membert> members;
  };
  using entryt = optionalt<defined_entryt>;

  typedef std::unordered_map<typet, entryt, irep_hash> cachet;

  // the 'mutable' is allow const methods above
  mutable cachet cache;

  const entryt &get_entry(const typet &type) const;
};

#endif // CPROVER_SOLVERS_FLATTENING_BOOLBV_WIDTH_H
