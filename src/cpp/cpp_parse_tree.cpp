/*******************************************************************\

Module: C++ Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Parser

#include "cpp_parse_tree.h"

void cpp_parse_treet::swap(cpp_parse_treet &cpp_parse_tree)
{
  cpp_parse_tree.items.swap(items);
}

void cpp_parse_treet::clear()
{
  items.clear();
}
