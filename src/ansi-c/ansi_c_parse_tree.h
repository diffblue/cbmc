/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_PARSE_TREE_H
#define CPROVER_ANSI_C_PARSE_TREE_H

#include "ansi_c_declaration.h"

class ansi_c_parse_treet
{
public:
  // the declarations
  typedef std::list<ansi_c_declarationt> itemst;
  itemst items;

  void swap(ansi_c_parse_treet &other);
  void clear();
  void output(std::ostream &out) const;
};

#endif
