/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_CLASS_LOADER_H
#define CPROVER_JAVA_CLASS_LOADER_H

#include <util/message.h>

#include "java_bytecode_parse_tree.h"

class java_class_loadert:public messaget
{
public:
  void operator()(const irep_idt &);
  void operator()(java_bytecode_parse_treet &);
  
  // maps class names to the parse trees
  typedef std::map<irep_idt, java_bytecode_parse_treet> class_mapt;
  class_mapt class_map;
};

#endif
