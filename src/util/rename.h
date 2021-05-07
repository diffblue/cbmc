/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_RENAME_H
#define CPROVER_UTIL_RENAME_H

//
// automated variable renaming
//

#include "irep.h"
#include "nodiscard.h"

class namespacet;

/// Build and identifier not yet present in the namespace \p ns based on \p
/// name. If \p name is not in the namespace, just returns \p name.
/// \param name: initial candidate identifier
/// \param ns: namespace
/// \param delimiter: character to separate the name and a newly generated
///   suffix
/// \return Identifier that is not yet part of the namespace.
NODISCARD irep_idt
get_new_name(const irep_idt &name, const namespacet &ns, char delimiter = '_');

#endif // CPROVER_UTIL_RENAME_H
