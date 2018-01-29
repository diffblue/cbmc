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
  // Default constructor does not use core models
  // for backward compatibility of unit tests
  java_class_loadert() :
    use_core_models(true)
  {}

  java_bytecode_parse_treet &operator()(const irep_idt &);

  void set_java_cp_include_files(std::string &);
  void add_load_classes(const std::vector<irep_idt> &);

  /// A function that yields a list of extra dependencies based on a class name.
  typedef std::function<std::vector<irep_idt>(const irep_idt &)>
    get_extra_class_refs_functiont;

  void set_extra_class_refs_function(get_extra_class_refs_functiont func);

  static std::string file_to_class_name(const std::string &);
  static std::string class_name_to_file(const irep_idt &);

  void add_jar_file(const std::string &f)
  {
    jar_files.push_back(f);
  }

  void load_entire_jar(java_class_loader_limitt &, const std::string &f);

  void read_jar_file(java_class_loader_limitt &, const irep_idt &);

  /// Attempts to load the class from the given jar.
  /// Returns true if found and loaded
  bool get_class_file(
    java_class_loader_limitt &class_loader_limit,
    const irep_idt &class_name,
    const std::string &jar_file,
    java_bytecode_parse_treet &parse_tree);

  /// Attempts to load the class from the internal core models.
  /// Returns true if found and loaded
  bool get_internal_class_file(
    java_class_loader_limitt &class_loader_limit,
    const irep_idt &class_name,
    java_bytecode_parse_treet &parse_tree);

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

  /// Load jar archive(from cache if already loaded)
  /// \param limit
  /// \param filename name of the file
  jar_filet &jar_pool(java_class_loader_limitt &limit,
                      const std::string &filename);

  /// Load jar archive(from cache if already loaded)
  /// \param limit
  /// \param buffer_name name of the original file
  /// \param pmem memory pointer to the contents of the file
  /// \param size size of the memory buffer
  /// Note that this mocks the existence of a file which may
  /// or may not exist since  the actual data bis retrieved from memory.
  jar_filet &jar_pool(java_class_loader_limitt &limit,
                      const std::string &buffer_name,
                      const void *pmem,
                      size_t size);

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

  /// Indicates that the core models should be loaded
  bool use_core_models;

private:
  std::map<std::string, jar_filet> m_archives;
  std::vector<irep_idt> java_load_classes;
  get_extra_class_refs_functiont get_extra_class_refs;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H
