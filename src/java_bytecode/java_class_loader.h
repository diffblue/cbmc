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
#include <util/fixed_keys_map_wrapper.h>

#include "java_bytecode_parse_tree.h"
#include "java_class_loader_limit.h"
#include "jar_file.h"

class java_class_loadert:public messaget
{
public:
  /// A map associating logical class names with the name of the .class file
  /// implementing it for all classes inside a single JAR file
  typedef std::map<irep_idt, std::string> jar_indext;

  typedef std::list<java_bytecode_parse_treet> parse_tree_with_overlayst;
  typedef std::map<irep_idt, parse_tree_with_overlayst>
    parse_tree_with_overridest_mapt;

  /// A function that yields a list of extra dependencies based on a class name.
  typedef std::function<std::vector<irep_idt>(const irep_idt &)>
    get_extra_class_refs_functiont;

  // Default constructor does not use core models
  // for backward compatibility of unit tests
  java_class_loadert() : use_core_models(true)
  {
  }

  parse_tree_with_overlayst &operator()(const irep_idt &class_name);

  /// Given a \p class_name (e.g. "java.lang.Thread") try to load the
  /// corresponding .class file by first scanning all .jar files whose
  /// pathname is stored in \ref jar_files, and if that doesn't work, then scan
  /// the actual filesystem using `config.java.classpath` as class path. Uses
  /// \p limit to limit the class files that it might (directly or indirectly)
  /// load and returns a default-constructed parse tree when unable to find the
  /// .class file.
  parse_tree_with_overlayst &get_parse_tree(
    java_class_loader_limitt &class_loader_limit,
    const irep_idt &class_name);

  void set_java_cp_include_files(std::string &java_cp_include_files)
  {
    this->java_cp_include_files = java_cp_include_files;
  }
  /// Sets a function that provides extra dependencies for a particular class.
  /// Currently used by the string preprocessor to note that even if we don't
  /// have a definition of core string types, it will nontheless give them
  /// certain known superclasses and interfaces, such as Serializable.
  void set_extra_class_refs_function(get_extra_class_refs_functiont func)
  {
    get_extra_class_refs = func;
  }
  /// Adds the list of classes to the load queue, forcing them to be loaded even
  /// without explicit reference
  /// \param classes: list of class identifiers
  void add_load_classes(const std::vector<irep_idt> &classes)
  {
    for(const auto &id : classes)
      java_load_classes.push_back(id);
  }
  void add_jar_file(const std::string &f)
  {
    jar_files.push_back(f);
  }
  void set_use_core_models(bool use_core_models)
  {
    this->use_core_models = use_core_models;
  }

  static std::string file_to_class_name(const std::string &);
  static std::string class_name_to_file(const irep_idt &);

  void load_entire_jar(java_class_loader_limitt &, const std::string &jar_path);

  const jar_indext &get_jar_index(const std::string &jar_path)
  {
    return jars_by_path.at(jar_path);
  }
  /// Map from class names to the bytecode parse trees
  fixed_keys_map_wrappert<parse_tree_with_overridest_mapt>
  get_class_with_overlays_map()
  {
    return fixed_keys_map_wrappert<parse_tree_with_overridest_mapt>(class_map);
  }
  const java_bytecode_parse_treet &get_original_class(
    const irep_idt &class_name)
  {
    return class_map.at(class_name).front();
  }

  /// Load jar archive or retrieve from cache if already loaded
  /// \param limit
  /// \param filename name of the file
  jar_filet &jar_pool(
    java_class_loader_limitt &limit, const std::string &filename);

  /// Load jar archive or retrieve from cache if already loaded
  /// \param limit
  /// \param buffer_name name of the original file
  /// \param pmem memory pointer to the contents of the file
  /// \param size size of the memory buffer
  /// Note that this mocks the existence of a file which may
  /// or may not exist since  the actual data bis retrieved from memory.
  jar_filet &jar_pool(
    java_class_loader_limitt &limit,
    const std::string &buffer_name,
    const void *pmem,
    size_t size);

private:
  /// Either a regular expression matching files that will be allowed to be
  /// loaded or a string of the form `@PATH` where PATH is the file path of a
  /// json file storing an explicit list of files allowed to be loaded. See
  /// java_class_loader_limitt::setup_class_load_limit() for further
  /// information.
  std::string java_cp_include_files;

  /// List of filesystem paths to .jar files that will be used, in the given
  /// order, to find and load a class, provided its name (see \ref
  /// get_parse_tree).
  std::list<std::string> jar_files;

  /// Indicates that the core models should be loaded
  bool use_core_models;

  /// Classes to be explicitly loaded
  std::vector<irep_idt> java_load_classes;
  get_extra_class_refs_functiont get_extra_class_refs;

  /// The jar_indext for each jar file we've read
  std::map<std::string, jar_indext> jars_by_path;

  /// Jar files that have been loaded
  std::map<std::string, jar_filet> m_archives;
  /// Map from class names to the bytecode parse trees
  parse_tree_with_overridest_mapt class_map;

  typedef optionalt<std::reference_wrapper<const jar_indext>>
    jar_index_optcreft;
  jar_index_optcreft read_jar_file(
    java_class_loader_limitt &class_loader_limit,
    const std::string &jar_path);
  optionalt<java_bytecode_parse_treet> get_class_from_jar(
    const irep_idt &class_name,
    const std::string &jar_file,
    java_class_loader_limitt &class_loader_limit);
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H
