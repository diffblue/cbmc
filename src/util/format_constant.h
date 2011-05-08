/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_FORMAT_CONSTANT_H
#define CPROVER_FORMAT_CONSTANT_H

#include "expr.h"
#include "format_spec.h"

class format_constantt:public format_spect
{
public:
  std::string operator()(const exprt &expr);
};

#endif
