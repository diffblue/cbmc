/*******************************************************************\

Module: Local variables whose address is taken

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

#ifndef CPROVER_LOCALS_H
#define CPROVER_LOCALS_H

#include <goto-programs/goto_functions.h>

class localst
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;

  explicit localst(const goto_functiont &goto_function)
  {
    build(goto_function);
  }

  void output(std::ostream &out) const;
  
  inline bool is_local(const irep_idt &identifier) const
  {
    return locals_map.find(identifier)!=locals_map.end();
  }

  typedef std::map<irep_idt, typet> locals_mapt;
  locals_mapt locals_map;
  
protected:
  void build(const goto_functiont &goto_function);
};

static inline std::ostream &operator << (
  std::ostream &out, const localst &locals)
{
  locals.output(out);
  return out;
}

#endif
