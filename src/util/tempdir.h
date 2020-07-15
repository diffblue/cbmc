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
  explicit temp_dirt(const std::string &name_template);
  ~temp_dirt();

  temp_dirt(const temp_dirt &) = delete;

  temp_dirt(temp_dirt &&other)
  {
    path.swap(other.path);
  }

  std::string operator()(const std::string &file);

  void clear();

  std::string path;
};

#endif // CPROVER_UTIL_TEMPDIR_H
