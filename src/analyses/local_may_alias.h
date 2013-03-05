/*******************************************************************\

Module: Field-sensitive, location-sensitive may-alias analysis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOCAL_MAY_ALIAS_H
#define CPROVER_LOCAL_MAY_ALIAS_H

#include <iostream>

#include <goto-programs/goto_program.h>

/*******************************************************************\

   Class: local_may_aliast
   
 Purpose:

\*******************************************************************/

class local_may_aliast
{
public:
  local_may_aliast(goto_programt &goto_program)
  {
    build(goto_program);
  }

  #if 0
  inline const object_id_sett &operator[](const object_idt &object_id)
  {
    value_mapt::const_iterator it=value_map.find(object_id);
    if(it!=value_map.end()) return it->second;
    return empty_set;
  }
  #endif

  void output(std::ostream &out) const;
  
  inline bool operator()(const exprt &e1, const exprt &e2)
  {
    return may_alias(e1, e2);
  }
          
protected:
  void build(goto_programt &goto_program);
  
  bool may_alias(const exprt &e1, const exprt &e2);
};

static inline std::ostream &operator << (
  std::ostream &out,
  const local_may_aliast &local_may_alias)
{
  local_may_alias.output(out);
  return out;
}

#endif
