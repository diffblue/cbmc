/*******************************************************************\

Module: mz_zip library wrapper

Author: Diffblue Ltd

\*******************************************************************/

#ifndef CPROVER_JAVA_BYTECODE_MZ_ZIP_ARCHIVE_H
#define CPROVER_JAVA_BYTECODE_MZ_ZIP_ARCHIVE_H

#include <string>
#include <memory>

/// State of the mz_zip_archive object
class mz_zip_archive_statet;

/// Thin object-oriented wrapper around the MZ Zip library
/// Zip file reader and extractor. Not thread safe. Move only.
class mz_zip_archivet final
{
public:
  /// Open a zip archive
  /// \param filename: Path of the zip archive
  /// \throw Throws std::runtime_error if file cannot be opened
  explicit mz_zip_archivet(const std::string &filename);

  /// Loads a zip buffer
  /// \param data: pointer to the memory buffer
  /// \param size: size of the buffer
  /// \throw Throws std::runtime_error if file cannot be opened
  mz_zip_archivet(const void *data, size_t size);

  mz_zip_archivet(const mz_zip_archivet &)=delete;
  mz_zip_archivet &operator=(const mz_zip_archivet &)=delete;
  /// Move constructor. Doesn't throw. Leaves other object invalidated.
  mz_zip_archivet(mz_zip_archivet &&other);
  /// Move assignment. Doesn't throw. Replaces this object's state
  /// with other object's state. Invalidates other object.
  mz_zip_archivet &operator=(mz_zip_archivet &&other);
  ~mz_zip_archivet();

  /// Get number of files in the archive
  size_t get_num_files();
  /// Get file name of nth file in the archive
  /// \param index: id of the file in the archive
  /// \return Name of the file in the archive
  std::string get_filename(size_t index);
  /// Get contents of nth file in the archive
  /// \param index: id of the file in the archive
  /// \throw Throws std::runtime_error if file cannot be extracted
  /// \return Contents of the file in the archive
  std::string extract(size_t index);
private:
  std::unique_ptr<mz_zip_archive_statet> m_state;
};

#endif // CPROVER_JAVA_BYTECODE_MZ_ZIP_ARCHIVE_H
