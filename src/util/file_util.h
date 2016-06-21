/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FILE_UTIL_H
#define CPROVER_FILE_UTIL_H

#include <string>

void delete_directory(const std::string &path);

std::string get_current_working_directory();

std::string concat_dir_file(const std::string &directory,
                            const std::string &file_name);

bool is_dot_i_file(const std::string &path);

#endif
