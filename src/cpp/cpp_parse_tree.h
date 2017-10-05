/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#ifndef CPROVER_CPP_CPP_PARSE_TREE_H
#define CPROVER_CPP_CPP_PARSE_TREE_H

#include "cpp_item.h"

class cpp_parse_treet
{
public:
  // the (top-level) declarations/definitions

  using itemst = std::list<cpp_itemt>;
  itemst items;

  void swap(cpp_parse_treet &cpp_parse_tree);
  void clear();
};

#endif // CPROVER_CPP_CPP_PARSE_TREE_H
