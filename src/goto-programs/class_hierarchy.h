/*******************************************************************\

Module: Class Hierarchy

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_CLASS_HIERARCHY_H
#define CPROVER_GOTO_PROGRAMS_CLASS_HIERARCHY_H

#include <iosfwd>
#include <map>

#include <util/namespace.h>

class class_hierarchyt
{
public:
  typedef std::vector<irep_idt> idst;

  class entryt
  {
  public:
    idst parents, children;
  };

  typedef std::map<irep_idt, entryt> class_mapt;
  class_mapt class_map;

  void operator()(const symbol_tablet &);

  // transitively gets all children
  idst get_children_trans(const irep_idt &id) const
  {
    idst result;
    get_children_trans_rec(id, result);
    return result;
  }

  // transitively gets all parents
  idst get_parents_trans(const irep_idt &id) const
  {
    idst result;
    get_parents_trans_rec(id, result);
    return result;
  }

  void output(std::ostream &) const;

protected:
  void get_children_trans_rec(const irep_idt &, idst &) const;
  void get_parents_trans_rec(const irep_idt &, idst &) const;
};

std::ostream &output_dot(std::ostream &ostr, const class_hierarchyt &hierarchy);

#endif // CPROVER_GOTO_PROGRAMS_CLASS_HIERARCHY_H
