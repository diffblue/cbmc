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

#include "jar_file.h"
#include "jar_pool.h"
#include "java_bytecode_parse_tree.h"
#include "java_class_loader_limit.h"

/// Class responsible to load .class files. Either directly from a specific
/// file, from a classpath specification or from a Java archive (JAR) file.
class java_class_loadert:public messaget
{
public:
  /// A map associating logical class names with the name of the .class file
  /// implementing it for all classes inside a single JAR file
  typedef std::map<irep_idt, std::string> jar_indext;

  /// A list of parse trees supporting overlay classes
  typedef std::list<java_bytecode_parse_treet> parse_tree_with_overlayst;
  /// A map from class names to list of parse tree where multiple entries can
  /// exist in case of overlay classes.
  typedef std::map<irep_idt, parse_tree_with_overlayst>
    parse_tree_with_overridest_mapt;

  /// A function that yields a list of extra dependencies based on a class name.
  typedef std::function<std::vector<irep_idt>(const irep_idt &)>
    get_extra_class_refs_functiont;

  java_class_loadert()
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

  /// Set the argument of the class loader limit \ref java_class_loader_limitt
  /// \param java_cp_include_files: argument string for java_class_loader_limit
  void set_java_cp_include_files(const std::string &java_cp_include_files)
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

  /// Clear all classpath entries
  void clear_classpath()
  {
    classpath_entries.clear();
  }

  /// Appends an entry to the class path, used for loading classes.  The
  /// argument may be
  /// 1) The name of a directory, used for searching for .class files
  /// 2) The name of a JAR file
  void add_classpath_entry(const std::string &);

  static std::string file_to_class_name(const std::string &);
  static std::string class_name_to_file(const irep_idt &);

  std::vector<irep_idt> load_entire_jar(const std::string &jar_path);

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

  /// a cache for jar_filet, by path name
  jar_poolt jar_pool;

private:
  /// Either a regular expression matching files that will be allowed to be
  /// loaded or a string of the form `@PATH` where PATH is the file path of a
  /// json file storing an explicit list of files allowed to be loaded. See
  /// java_class_loader_limitt::setup_class_load_limit() for further
  /// information.
  std::string java_cp_include_files;

  /// An entry in the classpath
  struct classpath_entryt
  {
    using kindt = enum { JAR, DIRECTORY };
    kindt kind;
    std::string path;

    classpath_entryt(kindt _kind, const std::string &_path)
      : kind(_kind), path(_path)
    {
    }
  };

  /// List of entries in the classpath
  std::list<classpath_entryt> classpath_entries;

  /// Classes to be explicitly loaded
  std::vector<irep_idt> java_load_classes;
  get_extra_class_refs_functiont get_extra_class_refs;

  /// The jar_indext for each jar file we've read
  std::map<std::string, jar_indext> jars_by_path;

  /// Map from class names to the bytecode parse trees
  parse_tree_with_overridest_mapt class_map;

  typedef optionalt<std::reference_wrapper<const jar_indext>>
    jar_index_optcreft;

  jar_index_optcreft read_jar_file(
    const std::string &jar_path);

  optionalt<java_bytecode_parse_treet> get_class_from_jar(
    const irep_idt &class_name,
    const std::string &jar_file,
    const jar_indext &jar_index);
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H
