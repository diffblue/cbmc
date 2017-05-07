/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#include "designator.h"

#include <ostream>

void designatort::print(std::ostream &out) const
{
  for(index_listt::const_iterator it=index_list.begin();
      it!=index_list.end();
      ++it)
  {
    if(it!=index_list.begin())
      out << ", ";
    out << it->type.id() << " " << it->index << "/" << it->size;
  }
}
