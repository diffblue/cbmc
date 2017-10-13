/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_FILE_UTIL_H
#define CPROVER_UTIL_FILE_UTIL_H

#include <string>
#include <vector>
#include <cstdint>
#include <iosfwd>
#include <stdexcept>

#ifdef _WIN32
#define PATH_SEPARATOR '\\'
#else
#define PATH_SEPARATOR '/'
#endif

/// Exception thrown by some file utilities on error.
class fileutil_error:public std::runtime_error
{
  using std::runtime_error::runtime_error;
};

bool fileutil_is_file(const std::string &pathname);
bool fileutil_is_directory(const std::string &pathname);

uint64_t fileutil_file_size(const std::string &file_pathname);

std::string fileutil_path_filename(const std::string &file_pathname);
std::string fileutil_path_dirname(const std::string &file_pathname);
std::string fileutil_remove_extension(const std::string &filename);
std::string fileutil_absolute_path(const std::string &path);
void fileutil_split_path(
  const std::string &path, std::vector<std::string>& output);
std::string fileutil_join_path(std::vector<std::string> const &parts);
std::string fileutil_concat_dir_file(
  const std::string &directory,
  const std::string &file_name);
std::string fileutil_get_common_prefix(
  const std::string &path1,
  const std::string &path2);
std::string fileutil_get_relative_path(
  const std::string &path,
  const std::string &directory);

void fileutil_create_directory(const std::string &dirname);
void fileutil_create_directories(const std::string &dirname);
void fileutil_delete_directory(const std::string &path);
std::string fileutil_get_current_working_directory();

std::string fileutil_make_valid_filename(std::string filename);

#endif // CPROVER_UTIL_FILE_UTIL_H
