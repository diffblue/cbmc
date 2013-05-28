/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_PARSE_TREE_H
#define CPROVER_JAVA_BYTECODE_PARSE_TREE_H

#include <util/std_code.h>

class java_bytecode_parse_treet
{
public:
  class itemt
  {
  public:
    irep_idt name;
    typet type;

    typedef std::vector<codet> instructionst;
    instructionst instructions;
  };
  
  typedef std::list<itemt> itemst;
  itemst items;

  void swap(java_bytecode_parse_treet &other);
  void clear();
  void output(std::ostream &out) const;
};

#endif
