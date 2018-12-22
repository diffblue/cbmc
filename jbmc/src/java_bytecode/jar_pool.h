/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAR_POOL_H
#define CPROVER_JAVA_BYTECODE_JAR_POOL_H

#include <map>
#include <string>

class jar_filet;

/// A chache for jar_filet objects, by file name
class jar_poolt
{
public:
  /// Load jar archive or retrieve from cache if already loaded
  /// \param jar_path: name of the file
  // Throws an exception if the file does not exist
  jar_filet &operator()(const std::string &jar_path);

  /// Add a jar archive or retrieve from cache if already added.
  /// Note that this mocks the existence of a file which may
  /// or may not exist since the actual data is retrieved from memory.
  /// \param buffer_name: name of the original file
  /// \param pmem: memory pointer to the contents of the file
  /// \param size: size of the memory buffer
  jar_filet &
  add_jar(const std::string &buffer_name, const void *pmem, size_t size);

protected:
  /// Jar files that have been loaded
  std::map<std::string, jar_filet> m_archives;
};

#endif // CPROVER_JAVA_BYTECODE_JAVA_CLASS_LOADER_H
