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

void delete_directory(const std::string &path);

std::string get_current_working_directory();

std::string concat_dir_file(
  const std::string &directory,
  const std::string &file_name);

/// These functions provide us disc-related functionality, like manipulation
/// with disc paths (concatenation/splitting), checking for existence of files,
/// etc.

bool fileutl_file_exists(std::string const &pathname);

bool fileutl_is_directory(std::string const &pathname);

uint64_t fileutl_file_size(std::string const &file_pathname);

std::string fileutl_parse_name_in_pathname(std::string const &file_pathname);

std::string fileutl_parse_path_in_pathname(std::string const &file_pathname);

std::string fileutl_remove_extension(std::string const &filename);

void fileutl_create_directory(std::string const &pathname);
void fileutl_delete_directory(std::string const &pathname);

std::string fileutl_concatenate_file_paths(
  std::string const &left_path,
  std::string const &right_path);

std::string fileutl_absolute_path(std::string const &path);

std::string fileutl_normalise_path(std::string const &path);

void fileutl_split_pathname(
  std::string const &pathname,
  std::vector<std::string>& output);

std::string fileutl_join_path_parts(std::vector<std::string> const &parts);

std::string fileutl_get_common_prefix(
  std::string const &pathname1,
  std::string const &pathname2);

std::string fileutl_get_relative_path(
  std::string const &pathname,
  std::string const &directory);

std::string make_valid_filename(std::string filename);

#endif // CPROVER_UTIL_FILE_UTIL_H
