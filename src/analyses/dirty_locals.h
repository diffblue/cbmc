/*******************************************************************\

Module: Local variables whose address is taken

Author: Daniel Kroening

Date: March 2013

\*******************************************************************/

#ifndef CPROVER_DIRTY_LOCALS_H
#define CPROVER_DIRTY_LOCALS_H

#include <namespace.h>
#include <goto-programs/goto_program.h>

class dirty_localst
{
public:
  dirty_localst(
    const goto_programt &goto_program,
    const namespacet &ns)
  {
    build(goto_program, ns);
  }

  void output(std::ostream &out) const;
  
  bool operator()(const irep_idt &id) const
  {
    return dirty.find(id)!=dirty.end();
  }
  
protected:
  void build(
    const goto_programt &goto_program,
    const namespacet &ns);

  // locals that might be accessed via a pointer
  typedef std::set<irep_idt> dirtyt;
  dirtyt dirty;
  
  void find_dirty(
    const exprt &expr,
    const namespacet &ns);
};

static inline std::ostream &operator << (
  std::ostream &out, const dirty_localst &dirty_locals)
{
  dirty_locals.output(out);
  return out;
}

#endif
