/*******************************************************************\

Module: Field-sensitive, location-insensitive points-to analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_INSTRUMENT_POINTS_TO_H
#define CPROVER_GOTO_INSTRUMENT_POINTS_TO_H

#include <ostream>

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

  inline void operator()(goto_functionst &goto_functions)
  {
    // build the CFG data structure
    cfg(goto_functions);
    
    // iterate
    fixedpoint();
  }

  inline const object_id_sett &operator[](const object_idt &object_id)
  {
    value_mapt::const_iterator it=value_map.find(object_id);
    if(it!=value_map.end()) return it->second;
    return empty_set;
  }

  void output(std::ostream &out) const;
  
  inline friend std::ostream &operator << (
    std::ostream &out, const points_tot &points_to)
  {
    points_to.output(out);
    return out;
  }
          
protected:
  struct cfg_nodet
  {
    cfg_nodet()
    {
    }
  };

  typedef cfg_baset<cfg_nodet> cfgt;
  cfgt cfg;

  typedef std::map<object_idt, object_id_sett> value_mapt;
  value_mapt value_map;
  
  void fixedpoint();
  bool transform(cfgt::iterator);
  
  const object_id_sett empty_set;
};

std::ostream &operator << (std::ostream &, const points_tot &);

#endif
