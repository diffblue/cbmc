/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_FORMAT_CONSTANT_H
#define CPROVER_UTIL_FORMAT_CONSTANT_H

#include <string>

#include "format_spec.h"

class exprt;

class format_constantt:public format_spect
{
public:
  std::string operator()(const exprt &expr);
};

#endif // CPROVER_UTIL_FORMAT_CONSTANT_H
