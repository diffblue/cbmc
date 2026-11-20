/*******************************************************************\

Module: Conservative approximation of inline assembly

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Conservative approximation of inline assembly statements whose
/// instructions are not modeled: everything the statement may change is
/// assigned a nondeterministic value.

#ifndef CPROVER_ASSEMBLER_ASM_APPROXIMATION_H
#define CPROVER_ASSEMBLER_ASM_APPROXIMATION_H

#include <util/expr.h>
#include <util/irep.h>
#include <util/std_expr.h>

#include <optional>
#include <vector>

class goto_programt;
class namespacet;
class source_locationt;
class symbol_table_baset;

/// The C-level footprint of an inline assembly statement: what the statement
/// may read and write.
struct asm_footprintt
{
  /// Expressions the statement may read. These are evaluated (and hence
  /// subject to the usual checks) before the statement.
  std::vector<exprt> reads;

  /// Lvalues the statement may write.
  std::vector<exprt> writes;

  /// Expressions whose values the statement may use as addresses: the objects
  /// they point to may be written. Arrays decay to the address of their first
  /// element, casts to integer types are looked through, and the pointer
  /// members of structs and unions are included.
  std::vector<exprt> addresses;

  /// Whether the statement may access memory not described by its operands
  /// (a "memory" clobber, basic assembly, or an MSVC-style block).
  bool arbitrary_memory = false;
};

/// Builds the instructions that conservatively approximate an inline assembly
/// statement given its footprint. The objects of static lifetime are
/// computed once and shared across statements.
class asm_approximationt
{
public:
  explicit asm_approximationt(symbol_table_baset &_symbol_table)
    : symbol_table(_symbol_table)
  {
  }

  /// Appends to \p dest instructions that
  /// 1. evaluate the reads of \p footprint;
  /// 2. record the addresses of the writes and the values of the addresses
  ///    of \p footprint in temporaries;
  /// 3. assign nondeterministic values to the objects the addresses point to;
  /// 4. if \p footprint has arbitrary memory accesses: assign
  ///    nondeterministic values to the objects of static lifetime, to the
  ///    objects that pointers stored in objects of static lifetime point to,
  ///    and to \p address_taken_locals;
  /// 5. assign nondeterministic values to the writes;
  /// 6. assign a nondeterministic rounding mode.
  /// Objects that are reachable only through other pointers (for example, a
  /// caller's local variables or heap objects not referenced by an object of
  /// static lifetime) are not changed.
  /// \param footprint: What the statement may read and write
  /// \param address_taken_locals: The local variables of the enclosing
  ///   function whose address is taken
  /// \param function_id: Name of the enclosing function, which temporaries
  ///   are added to
  /// \param source_location: Location of the statement
  /// \param dest: Goto program to append the instructions to
  void operator()(
    const asm_footprintt &footprint,
    const std::vector<symbol_exprt> &address_taken_locals,
    const irep_idt &function_id,
    const source_locationt &source_location,
    goto_programt &dest);

  /// \return The local variables of \p body whose address is taken, sorted by
  ///   name and excluding objects of static lifetime and constant objects.
  static std::vector<symbol_exprt>
  address_taken_locals(const goto_programt &body, const namespacet &ns);

  /// Appends to \p dest the expressions contained in \p expr that may hold
  /// addresses, as described for \ref asm_footprintt::addresses.
  static void collect_addresses(
    const exprt &expr,
    const namespacet &ns,
    std::vector<exprt> &dest);

private:
  symbol_table_baset &symbol_table;

  /// The modifiable objects of static lifetime, sorted by name; computed on
  /// first use.
  std::optional<std::vector<symbol_exprt>> static_objects;

  const std::vector<symbol_exprt> &get_static_objects();
};

#endif // CPROVER_ASSEMBLER_ASM_APPROXIMATION_H
