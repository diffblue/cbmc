/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/


#ifndef CPROVER_UTIL_TEMPDIR_H
#define CPROVER_UTIL_TEMPDIR_H

#include <string>

std::string get_temporary_directory(const std::string &name_template);

// Produces a temporary directory,
// and deletes it upon destruction.
class temp_dirt
{
public:
  std::string path;

  std::string operator()(const std::string &file);

  void clear();

  explicit temp_dirt(const std::string &name_template);
  ~temp_dirt();
};

#endif // CPROVER_UTIL_TEMPDIR_H
