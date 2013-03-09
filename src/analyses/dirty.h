/*******************************************************************\

Module: Variables whose address is taken

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

#ifndef CPROVER_DIRTY_H
#define CPROVER_DIRTY_H

#include <goto-programs/goto_functions.h>

class dirtyt
{
public:
  typedef goto_functionst::goto_functiont goto_functiont;

  explicit dirtyt(const goto_functiont &goto_function)
  {
    build(goto_function);
  }

  void output(std::ostream &out) const;
  
  bool is_dirty(const irep_idt &id) const
  {
    return dirty.find(id)!=dirty.end();
  }

protected:
  void build(const goto_functiont &goto_function);

  // variables whose address is taken
  typedef std::set<irep_idt> id_sett;
  id_sett dirty;
  
  void find_dirty(const exprt &expr);
  void find_dirty_address_of(const exprt &expr);
};

static inline std::ostream &operator << (
  std::ostream &out, const dirtyt &dirty)
{
  dirty.output(out);
  return out;
}

#endif
