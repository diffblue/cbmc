/*******************************************************************\

Module: Class Hierarchy

Author: Daniel Kroening

Date: April 2016

\*******************************************************************/

#ifndef CPROVER_CLASS_HIERARCHY_H
#define CPROVER_CLASS_HIERARCHY_H

#include <iosfwd>

#include <util/symbol_table.h>

class class_hierarchyt
{
public:
  class entryt
  {
  public:
    irep_idt parent;
    typedef std::vector<irep_idt> childrent;
    childrent children;
  };

  typedef std::map<irep_idt, entryt> class_mapt;
  class_mapt class_map;
  
  void operator()(const symbol_tablet &);

  // transitively gets all children
  void get_children(const irep_idt &, std::vector<irep_idt> &) const;
  
  irep_idt get_parent(const irep_idt &) const;
  
  void output(std::ostream &) const;
};

#endif
