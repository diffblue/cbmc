/*******************************************************************\

Module: 

Author: Daniel Kroening

\*******************************************************************/

#ifndef CPROVER_TEMPFILE_H
#define CPROVER_TEMPFILE_H

#include <string>

std::string get_temporary_file(
  const std::string &prefix,
  const std::string &suffix);

#endif
