/*******************************************************************\

Module: ANSI-C Language Type Checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Type Checking

#ifndef CPROVER_ANSI_C_PADDING_H
#define CPROVER_ANSI_C_PADDING_H

#include <util/irep.h>
#include <util/mp_arith.h>

#include <optional>

class namespacet;
class struct_typet;
class typet;
class union_typet;

/// \return the value of the layout attribute \p id (ID_C_alignment,
///   ID_C_declaration_alignment, or ID_C_pragma_pack) of \p src, or an empty
///   optional when \p src has no such attribute, or the attribute has no
///   constant value (as for `__attribute__((aligned))` without argument)
std::optional<bytest> layout_attribute(const irept &src, const irep_idt &id);

bytest alignment(const typet &type, const namespacet &);
void add_padding(struct_typet &type, const namespacet &);
void add_padding(union_typet &type, const namespacet &);

#endif // CPROVER_ANSI_C_PADDING_H
