/*******************************************************************\

Module: Modified expression replacement for constant propagator

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_ANALYSES_REPLACE_SYMBOL_EXT_H
#define CPROVER_ANALYSES_REPLACE_SYMBOL_EXT_H

#include <util/replace_symbol.h>

class replace_symbol_extt:public replace_symbolt
{
public:
  virtual bool replace(exprt &dest) const;
};

#endif // CPROVER_ANALYSES_REPLACE_SYMBOL_EXT_H
