/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_PARSE_TREE_H
#define CPROVER_CPP_PARSE_TREE_H

#include "cpp_item.h"

class cpp_parse_treet
{
public:
  // the (top-level) declarations/definitions

  typedef std::list<cpp_itemt> itemst;
  itemst items;

  void swap(cpp_parse_treet &cpp_parse_tree);
  void clear();
};

#endif
