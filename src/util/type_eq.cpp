/*******************************************************************\

Module: Type equality

Author: Daniel Kroening, kroening@kroening.com
        Maria Svorenova, maria.svorenova@diffblue.com

\*******************************************************************/

/// \file
/// Type equality

#include "type_eq.h"

#include "invariant.h"
#include "namespace.h"
#include "std_types.h"
#include "symbol.h"

/// Check types for equality at the top level. If either of the types is a
/// symbol type, i.e., a reference into the symbol table, retrieve it from
/// the namespace and compare but don't do this recursively. For equality
/// across all level in the hierarchy use \ref base_type_eq.
/// Example:
/// - `symbol_typet("a")` and `ns.lookup("a").type` will compare equal,
/// - `struct_typet {symbol_typet("a")}` and `struct_typet {ns.lookup("a")
///   .type}` will not compare equal.
/// \param type1: The first type to compare.
/// \param type2: The second type to compare.
/// \param ns: The namespace, needed for resolution of symbols.
bool type_eq(const typet &type1, const typet &type2, const namespacet &ns)
{
  if(type1==type2)
    return true;

  return false;
}
