/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H
#define CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H

#include <map>
#include <regex>
#include <set>

#include <util/message.h>

#include "java_bytecode_parse_tree.h"
#include "java_class_loader_limit.h"
#include "jar_file.h"

class java_class_loadert:public messaget
{
public:
  java_bytecode_parse_treet &operator()(const irep_idt &);

  void set_java_cp_include_files(std::string &);

  static std::string file_to_class_name(const std::string &);
  static std::string class_name_to_file(const irep_idt &);

  void add_jar_file(const std::string &f)
  {
    jar_files.push_back(f);
  }

  void load_entire_jar(java_class_loader_limitt &, const std::string &f);

  void read_jar_file(java_class_loader_limitt &, const irep_idt &);

  /// Given a \p class_name (e.g. "java.lang.Thread") try to load the
  /// corresponding .class file by first scanning all .jar files whose
  /// pathname is stored in \ref jar_files, and if that doesn't work, then scan
  /// the actual filesystem using `config.java.classpath` as class path. Uses
  /// \p limit to limit the class files that it might (directly or indirectly)
  /// load and returns a default-constructed parse tree when unable to find the
  /// .class file.
  java_bytecode_parse_treet &get_parse_tree(
    java_class_loader_limitt &limit, const irep_idt &class_name);

  /// Maps class names to the bytecode parse trees.
  typedef std::map<irep_idt, java_bytecode_parse_treet> class_mapt;
  class_mapt class_map;

  /// Maps .jar filesystem paths to jar_filet objects (stored inside).
  /// Responsible for loading new jar files when they are first referenced.
  jar_poolt jar_pool;

  /// An object of this class represents the information of _a single JAR file_
  /// that is relevant for a class loader: a map associating logical class names
  /// with with handles (struct entryt) that describe one .class file inside the
  /// JAR. Currently the handle only contains the name of the .class file.
  class jar_map_entryt
  {
  public:
    struct entryt
    {
      std::string class_file_name;
    };

    /// Maps class names to jar file entries.
    typedef std::map<irep_idt, entryt> entriest;
    entriest entries;
  };

  /// Maps .jar filesystem paths to .class file descriptors (see
  /// jar_map_entryt).
  typedef std::map<irep_idt, jar_map_entryt> jar_mapt;
  jar_mapt jar_map;

  /// List of filesystem paths to .jar files that will be used, in the given
  /// order, to find and load a class, provided its name (see \ref
  /// get_parse_tree).
  std::list<std::string> jar_files;

  /// Either a regular expression matching files that will be allowed to be
  /// loaded or a string of the form `@PATH` where PATH is the file path of a
  /// json file storing an explicit list of files allowed to be loaded. See
  /// java_class_loader_limitt::setup_class_load_limit() for further
  /// information.
  std::string java_cp_include_files;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H
