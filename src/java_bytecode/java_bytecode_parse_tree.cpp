/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_parse_tree.h"

/*******************************************************************\

Function: java_bytecode_parse_treet::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::swap(java_bytecode_parse_treet &java_bytecode_parse_tree)
{
  java_bytecode_parse_tree.items.swap(items);
}

/*******************************************************************\

Function: java_bytecode_parse_treet::clear

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::clear()
{
  items.clear();
}

/*******************************************************************\

Function: java_bytecode_parse_treet::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_parse_treet::output(std::ostream &out) const
{
  #if 0
  for(itemst::const_iterator
      it=items.begin();
      it!=items.end();
      it++)
  {
    symbolt tmp;
    it->to_symbol(tmp);
    out << tmp;
  }
  #endif
}
