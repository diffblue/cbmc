/*******************************************************************\

Module: JAR File Reading

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// JAR File Reading

#ifndef CPROVER_JAVA_BYTECODE_JAR_FILE_H
#define CPROVER_JAVA_BYTECODE_JAR_FILE_H

#define _LARGEFILE64_SOURCE 1
#include "miniz/miniz.h"

#include <string>
#include <vector>
#include <map>
#include <regex>
#include <util/message.h>

#include "java_class_loader_limit.h"

/// An in-memory representation of a JAR file, consisting of a handler to a zip
/// file (field \ref zip) and a map from file names inside the zip file to the
/// index they occupy in the root directory (field \ref filtered_jar).
///
/// Both fields are initialize by a call to open(). Method get_entry() reads a
/// file from the zip and returns it.
class jar_filet:public messaget
{
public:
  jar_filet():
    mz_ok(false)
    // `zip` will be initialized by open()
  {
  }

  ~jar_filet();

  /// Initializes \ref zip to store the JAR file pointed by \p filepath and
  /// loads the map \ref filtered_jar with the .class names allowed by \p limit.
  void open(java_class_loader_limitt &limit, const std::string &filepath);

  /// Test for error; 'true' means we are good.
  explicit operator bool() const { return mz_ok; }

  /// Reads the \ref zip field and returns a string storing the data contained
  /// in file \p name.
  std::string get_entry(const irep_idt &name);

  /// Maps the names of the files stored in the JAR file to the index they
  /// occupy (starting from 0) in the JAR central directory.  Populated by
  /// method open() above.
  typedef std::map<irep_idt, size_t> filtered_jart;
  filtered_jart filtered_jar;

  typedef std::map<std::string, std::string> manifestt;
  manifestt get_manifest();

protected:
  /// A handle representing the zip file
  mz_zip_archive zip;

  /// True iff the \ref zip field has been correctly initialized with a JAR file
  bool mz_ok;
};

/// A pool of jar_filet objects, indexed by the filesystem path name used to
/// load that jar_filet.
///
/// The state of the class is maintained by the field \ref file_map, a std::map
/// associating the path of a .jar file with its in-memory representation.
/// A call to
///
/// ```
///   operator()(limit, path)
/// ```
///
/// will either return a previously loaded jar_filet, if it is found in the map,
/// or will load that file (using jar_filet::open) and return a newly created
/// jar_filet.
class jar_poolt:public messaget
{
public:
  jar_filet &operator()(
    java_class_loader_limitt &class_loader_limit,
    const std::string &file_name)
  {
    file_mapt::iterator it=file_map.find(file_name);
    if(it==file_map.end())
    {
      jar_filet &jar_file=file_map[file_name];
      jar_file.set_message_handler(get_message_handler());
      jar_file.open(class_loader_limit, file_name);
      return jar_file;
    }
    else
      return file_map[file_name];
  }

protected:
  /// A map from filesystem paths to jar_filet objects
  typedef std::map<std::string, jar_filet> file_mapt;
  file_mapt file_map;
};

#endif // CPROVER_JAVA_BYTECODE_JAR_FILE_H
