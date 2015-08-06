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
  java_bytecode_parse_treet &operator()(const irep_idt &);
  
  // maps class names to the parse trees
  typedef std::map<irep_idt, java_bytecode_parse_treet> class_mapt;
  class_mapt class_map;

  // add a JAR file, which will be searched
  void add_jar_file(const irep_idt &);
  
  // add a .class file directly
  void add_class_file(const irep_idt &file);
  
  static std::string file_to_class_name(const std::string &);

protected:
  struct jar_entryt
  {
    std::size_t index;
    irep_idt jar_file_name;
  };
  
  // maps class names (no .class extension) to JAR file names
  typedef std::map<irep_idt, jar_entryt> class_jar_mapt;
  class_jar_mapt class_jar_map;
  
  // maps class names (no .class extension) to class file names
  typedef std::map<irep_idt, irep_idt> class_file_mapt;
  class_file_mapt class_file_map;
  
  // get a parse tree from JAR and then from .class files
  java_bytecode_parse_treet &get_parse_tree(const irep_idt &);
};

#endif
