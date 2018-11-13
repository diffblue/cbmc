/*******************************************************************\

Module: Pointer Dereferencing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Pointer Dereferencing

#ifndef CPROVER_POINTER_ANALYSIS_DEREFERENCE_CALLBACK_H
#define CPROVER_POINTER_ANALYSIS_DEREFERENCE_CALLBACK_H

#include <string>

#include "value_sets.h"

class guardt;
class exprt;
class symbolt;

/*! \brief TO_BE_DOCUMENTED
*/
class dereference_callbackt
{
public:
  virtual ~dereference_callbackt() = default;

  virtual void get_value_set(
    const exprt &expr,
    value_setst::valuest &value_set)=0;

  virtual bool has_failed_symbol(
    const exprt &expr,
    const symbolt *&symbol)=0;
};

#endif // CPROVER_POINTER_ANALYSIS_DEREFERENCE_CALLBACK_H
