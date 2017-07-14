/*******************************************************************\

 Module: Java Bytecode Language Conversion

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Handle selection of correct pointer type (for example changing abstract
/// classes to concrete versions).

#include "select_pointer_type.h"
#include <util/std_types.h>

/// Select what type should be used for a given pointer type. For the base class
/// we just use the supplied type. Derived classes can override this behaviour
/// to provide more sophisticated type selection
/// \param pointer_type: The pointer type replace
/// \return A pointer type where the subtype may have been modified
pointer_typet select_pointer_typet::convert_pointer_type(
  const pointer_typet &pointer_type) const
{
  return  pointer_type;
}
