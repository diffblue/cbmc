/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FILE_UTIL_H
#define CPROVER_FILE_UTIL_H

#include <string>

void delete_directory(const std::string &path);

std::string get_current_working_directory();

#endif
