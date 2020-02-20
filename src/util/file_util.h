/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_FILE_UTIL_H
#define CPROVER_UTIL_FILE_UTIL_H

#include <string>

// C++17 will allow us to use std::filesystem::path::remove_all
void delete_directory(const std::string &path);

// C++17 will allow us to use std::filesystem::current_path (for both get and
// set)
std::string get_current_working_directory();
void set_current_path(const std::string &path);

// C++17 will allow us to use std::filesystem::path(dir).append(file)
std::string concat_dir_file(const std::string &directory,
                            const std::string &file_name);

// C++17 will allow us to use std::filesystem::is_directory
bool is_directory(const std::string &path);

/// Create a directory with given path
/// C++17 will allow us to use std::filesystem::create_directory
/// \return true iff the directory was created
bool create_directory(const std::string &path);

/// Check whether file with given path exists.
/// C++17 will allow us to use std::filesystem::directory_entry(file).exists()
/// \return true iff the file exists
bool file_exists(const std::string &path);

// Delete a file with given path
/// C++17 will allow us to use std::filesystem::remove
/// \return true if the file was deleted, false if it did not exist
bool file_remove(const std::string &path);

/// Rename a file.
/// C++17 will allow us to use std::filesystem::rename
/// Throws an exception on failure.
void file_rename(const std::string &old_path, const std::string &new_path);

#endif // CPROVER_UTIL_FILE_UTIL_H
