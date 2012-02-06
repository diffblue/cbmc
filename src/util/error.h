/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ERROR_H
#define CPROVER_ERROR_H

#include <exception>
#include <sstream>
#include <iostream>

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

class error_str:public error_baset, public std::ostringstream
{
public:
  virtual const char* what() const throw()
  {
    return str().c_str();
  }
  
  virtual ~error_str() throw ()
  {
  }
  
  inline error_str()
  {
  }
  
  explicit inline error_str(const locationt &_location):
    error_baset(_location), std::ostringstream()
  {
  }
  
  explicit inline error_str(const char *string)
  {
    str(string);
  }

  explicit inline error_str(const std::string &string)
  {
    str(string);
  }
  
  inline error_str(const error_str &other):std::ostringstream()
  {
    str(other.str());
    location=other.location;
  }

  inline error_str(const locationt &_location, const std::string &string):
    error_baset(_location)
  {
    str(string);
  }
};

#endif
