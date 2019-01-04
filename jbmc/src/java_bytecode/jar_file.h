/*******************************************************************\

Module: Jar file reader

Author: Diffblue Ltd

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_JAR_FILE_H
#define CPROVER_JAVA_BYTECODE_JAR_FILE_H

#include <unordered_map>
#include <memory>
#include <string>
#include <vector>

#include <util/optional.h>

#include "mz_zip_archive.h"

/// Class representing a .jar archive. Uses miniz to decompress and index
/// archive.
class jar_filet final
{
public:
  /// Open java file for reading.
  /// \param filename: Name of the file
  /// \throw Throws std::runtime_error if file cannot be opened
  explicit jar_filet(const std::string &filename);

  /// Open a JAR file of size \p size loaded in memory at address \p data.
  /// \param data: memory buffer with the contents of the jar file
  /// \param size: size  of the memory buffer
  /// \throw Throws std::runtime_error if file cannot be opened
  jar_filet(const void *data, size_t size);

  jar_filet(const jar_filet &)=delete;
  jar_filet &operator=(const jar_filet &)=delete;
  jar_filet(jar_filet &&);
  jar_filet &operator=(jar_filet &&);
  ~jar_filet()=default;

  /// Get contents of a file in the jar archive.
  /// Returns nullopt if file doesn't exist.
  /// \param filename: Name of the file in the archive
  optionalt<std::string> get_entry(const std::string &filename);

  /// Get contents of the Manifest file in the jar archive as a key-value map
  /// (both as strings)
  std::unordered_map<std::string, std::string> get_manifest();

  /// Get list of filenames in the archive
  std::vector<std::string> filenames() const;

private:
  /// Loads the fileindex (m_name_to_index) with a map of loaded files to
  /// indices.
  void initialize_file_index();

  mz_zip_archivet m_zip_archive;

  /// Map of filename to the file index in the zip archive.
  std::unordered_map<std::string, size_t> m_name_to_index;
};

#endif // CPROVER_JAVA_BYTECODE_JAR_FILE_H
