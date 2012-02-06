/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ERROR_H
#define CPROVER_ERROR_H

#include <exception>
#include <sstream>

#include "location.h"

class error_baset:public exception
{
public:
  virtual const char* what() const throw()
  {
    return "";
  }
  
  locationt location;
};          

class error:public error_baset, public std::ostringstream
{
public:
  virtual const char* what() const throw()
  {
    return str().c_str();
  }
};          

#endif
