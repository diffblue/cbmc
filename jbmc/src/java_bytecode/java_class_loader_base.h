/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_BASE_H
#define CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_BASE_H

#include <util/irep.h>

#include "jar_pool.h"

#include <list>

class message_handlert;
struct java_bytecode_parse_treet;

/// Base class for maintaining classpath.
class java_class_loader_baset
{
public:
  /// Clear all classpath entries
  void clear_classpath()
  {
    classpath_entries.clear();
  }

  /// Appends an entry to the class path, used for loading classes.  The
  /// argument may be
  /// 1) The name of a directory, used for searching for .class files
  /// 2) The name of a JAR file
  void add_classpath_entry(const std::string &, message_handlert &);

  static std::string file_to_class_name(const std::string &);
  static std::string class_name_to_os_file(const irep_idt &);
  static std::string class_name_to_jar_file(const irep_idt &);

  /// a cache for jar_filet, by path name
  jar_poolt jar_pool;

protected:
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

  /// attempt to load a class from a classpath_entry
  std::optional<java_bytecode_parse_treet> load_class(
    const irep_idt &class_name,
    const classpath_entryt &,
    message_handlert &);

  /// attempt to load a class from a given jar file
  std::optional<java_bytecode_parse_treet> get_class_from_jar(
    const irep_idt &class_name,
    const std::string &jar_file,
    message_handlert &);

  /// attempt to load a class from a given directory
  std::optional<java_bytecode_parse_treet> get_class_from_directory(
    const irep_idt &class_name,
    const std::string &path,
    message_handlert &);
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_BASE_H
