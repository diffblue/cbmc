/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H
#define CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H

#include <util/message.h>

#include "java_bytecode_parse_tree.h"
#include "jar_file.h"

class java_class_loadert:public messaget
{
public:
  using parse_treet=java_bytecode_parse_treet;

  java_class_loadert()
  {
  }

  /// Given a \p class_name (e.g. "java.lang.Thread") try to load the
  /// corresponding .class file by first scanning all .jar files whose
  /// pathname is stored in \ref jar_files, and if that doesn't work, then scan
  /// the actual filesystem using `config.java.classpath` as class path.
  /// Returns a default-constructed parse tree when unable to find the
  /// .class file.
  parse_treet &operator()(const irep_idt &class_name);

  void add_classpath_entry(const std::string &f);
  void add_jar_from_memory(const void *pmem, size_t size);

  static std::string file_to_class_name(const std::string &);
  static std::string class_name_to_file(const irep_idt &);

private:
  std::map<irep_idt, parse_treet> class_map;

  /// List of entries (jars or directories) that will be used,
  /// in the given order, to find and load a class.
  struct entryt
  {
    entryt(const std::string &_path):path(_path)
    {
    }

    enum { JAR, DIRECTORY } kind;

    std::string path;
    optionalt<jar_filet> jar_file;
  };

  std::list<entryt> entries;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H
