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
#include "mz_zip_archive.h"

class java_class_loader_limitt;

/// Class representing a .jar archive
class jar_filet final
{
public:
  /// Open java file for reading
  /// \param limit Object limiting number of loaded .class files
  /// \param filename Name of the file
  /// \throw Throws std::runtime_error if file cannot be opened
  jar_filet(java_class_loader_limitt &limit, const std::string &filename);
  jar_filet(const jar_filet &)=delete;
  jar_filet &operator=(const jar_filet &)=delete;
  jar_filet(jar_filet &&);
  jar_filet &operator=(jar_filet &&);
  ~jar_filet()=default;
  /// Get contents of a file in the jar archive.
  /// Terminates the program if file doesn't exist
  /// \param filename Name of the file in the archive
  std::string get_entry(const std::string &filename);
  /// Get contents of the Manifest file in the jar archive
  std::unordered_map<std::string, std::string> get_manifest();
  /// Get list of filenames in the archive
  std::vector<std::string> filenames() const;
private:
  mz_zip_archivet m_zip_archive;
  /// Map of filename to the file index in the zip archive
  std::unordered_map<std::string, size_t> m_name_to_index;
};

#endif // CPROVER_JAVA_BYTECODE_JAR_FILE_H
