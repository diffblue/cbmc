/*******************************************************************\

Module: Implementations of some functions of typet

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Implementations of some functions of typet

#include "type.h"

/// Copy the provided type to the subtypes of this type.
/// \param type The type to add to subtypes
void typet::copy_to_subtypes(const typet &type)
{
  subtypes().push_back(type);
}

/// Move the provided type to the subtypes of this type. Destroys the
/// provided type.
/// \param type The type to add to subtypes
void typet::move_to_subtypes(typet &type)
{
  subtypest &sub=subtypes();
  sub.push_back(static_cast<const typet &>(get_nil_irep()));
  sub.back().swap(type);
}
