/*******************************************************************\

Module: Field-sensitive, location-insensitive points-to analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_POINTS_TO_H
#define CPROVER_GOTO_INSTRUMENT_POINTS_TO_H

#include <iosfwd>

#include <goto-programs/goto_functions.h>
#include <goto-programs/cfg.h>

#include "object_id.h"

/*******************************************************************\

   Class: points_tot

 Purpose:

\*******************************************************************/

class points_tot
{
public:
  points_tot()
  {
  }

  void operator()(goto_functionst &goto_functions)
  {
    // build the CFG data structure
    cfg(goto_functions);

    // iterate
    fixedpoint();
  }

  const object_id_sett &operator[](const object_idt &object_id)
  {
    value_mapt::const_iterator it=value_map.find(object_id);
    if(it!=value_map.end()) return it->second;
    return empty_set;
  }

  void output(std::ostream &out) const;

protected:
  typedef cfg_baset<empty_cfg_nodet> cfgt;
  cfgt cfg;

  typedef std::map<object_idt, object_id_sett> value_mapt;
  value_mapt value_map;

  void fixedpoint();
  bool transform(const cfgt::nodet&);

  const object_id_sett empty_set;
};

inline std::ostream &operator<<(
  std::ostream &out,
  const points_tot &points_to)
{
  points_to.output(out);
  return out;
}

#endif // CPROVER_GOTO_INSTRUMENT_POINTS_TO_H
