/*******************************************************************\

Module: 

Author: Daniel Kroening

\*******************************************************************/

#ifndef CPROVER_TEMPFILE_H
#define CPROVER_TEMPFILE_H

#include <string>

// Returns an unused file name for a writeable temporary file,
// and makes sure it exists.
std::string get_temporary_file(
  const std::string &prefix,
  const std::string &suffix);

// The below deletes the temporary file upon destruction,
// cleaning up after you in case of exceptions.
class temporary_filet
{
public:
  inline temporary_filet(
    const std::string &prefix,
    const std::string &suffix):
      name(get_temporary_file(prefix, suffix))
  {
  }
  
  // get the name
  inline std::string operator()() const
  {
    return name;
  }

  // will delete the file
  ~temporary_filet();

protected:
  std::string name;
};

#endif
