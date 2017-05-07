/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_parse_tree.h"

#include <ostream>

void ansi_c_parse_treet::swap(ansi_c_parse_treet &ansi_c_parse_tree)
{
  ansi_c_parse_tree.items.swap(items);
}

void ansi_c_parse_treet::clear()
{
  items.clear();
}

void ansi_c_parse_treet::output(std::ostream &out) const
{
  for(const auto &item : items)
  {
    item.output(out);
    out << "\n";
  }
}
