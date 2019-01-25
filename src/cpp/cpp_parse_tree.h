/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#ifndef CPROVER_CPP_CPP_PARSE_TREE_H
#define CPROVER_CPP_CPP_PARSE_TREE_H

#include "cpp_item.h"

#include <list>

class cpp_parse_treet
{
public:
  // the (top-level) declarations/definitions

  typedef std::list<cpp_itemt> itemst;
  itemst items;

  void swap(cpp_parse_treet &cpp_parse_tree);
  void clear();
};

class uninitialized_typet : public typet
{
public:
  uninitialized_typet() : typet(static_cast<const typet &>(get_nil_irep()))
  {
  }
};

#endif // CPROVER_CPP_CPP_PARSE_TREE_H
