/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_TEMPDIR_H
#define CPROVER_TEMPDIR_H

#include <string>

std::string get_temporary_directory(const std::string &name_template);

class temp_working_dirt
{
public:
  std::string old_working_directory;
  std::string path;
  
  explicit temp_working_dirt(const std::string &name_template);
  ~temp_working_dirt();
};

#endif
