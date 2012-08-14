/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_TEMPDIR_H
#define CPROVER_TEMPDIR_H

#include <string>

std::string get_temporary_directory(const std::string &name_template);

// Produces a temporary directory,
// and deletes it upon destruction.
class temp_dirt
{
public:
  std::string path;

  std::string operator()(const std::string &file);
  
  explicit temp_dirt(const std::string &name_template);
  ~temp_dirt();
};

// Produces a temporary directory,
// chdir()s there,
// and deletes it upon destruction,
// and goes back to the old working directory.
class temp_working_dirt:public temp_dirt
{
public:
  std::string old_working_directory;
  
  explicit temp_working_dirt(const std::string &name_template);  
  ~temp_working_dirt();
};

#endif
