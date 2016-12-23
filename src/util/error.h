/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_ERROR_H
#define CPROVER_UTIL_ERROR_H

#include <exception>
#include <sstream>

#include "location.h"

class error_baset:public std::exception
{
public:
  virtual const char* what() const throw()
  {
    return "";
  }

  virtual ~error_baset() throw ()
  {
  }

  inline error_baset()
  {
  }

  inline explicit error_baset(const locationt &_location):location(_location)
  {
  }

  locationt location;
};

class error_streamt:public error_baset, public std::ostringstream
{
public:
  virtual const char* what() const throw()
  {
    return str().c_str();
  }

  virtual ~error_streamt() throw()
  {
  }

  error_streamt()
  {
  }

  explicit error_streamt(const locationt &_location):
    error_baset(_location), std::ostringstream()
  {
  }

  explicit error_streamt(const char *string)
  {
    str(string);
  }

  explicit error_streamt(const std::string &string)
  {
    str(string);
  }

  error_streamt(const error_streamt &other):std::ostringstream()
  {
    str(other.str());
    location=other.location;
  }

  error_streamt(const locationt &_location, const std::string &string):
    error_baset(_location)
  {
    str(string);
  }
};

#endif // CPROVER_UTIL_ERROR_H
