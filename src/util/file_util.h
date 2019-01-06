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

#endif // CPROVER_UTIL_FILE_UTIL_H
