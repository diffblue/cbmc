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
  /// they point to, and all objects reachable from these, may be written.
  /// Arrays decay to the address of their first element, casts to integer
  /// types are looked through, and the pointer members of structs and unions
  /// are included.
  std::vector<exprt> addresses;

  /// Whether the statement may access memory not described by its operands
  /// (a "memory" clobber, basic assembly, or an MSVC-style block).
  bool arbitrary_memory = false;
};

/// Builds the instructions that conservatively approximate an inline assembly
/// statement given its footprint.
class asm_approximationt
{
public:
  explicit asm_approximationt(symbol_table_baset &_symbol_table)
    : symbol_table(_symbol_table)
  {
  }

  /// Appends to \p dest instructions that
  /// 1. evaluate the reads of \p footprint;
  /// 2. record the addresses of the writes in temporaries;
  /// 3. assign nondeterministic values to all objects reachable from the
  ///    addresses of \p footprint and, if \p footprint has arbitrary memory
  ///    accesses, from the objects of static lifetime and the address-taken
  ///    local variables of all functions on the call stack (a
  ///    `havoc_reachable` statement, which symbolic execution implements
  ///    using the value set);
  /// 4. assign nondeterministic values to the writes;
  /// 5. assign a nondeterministic rounding mode.
  /// \param footprint: What the statement may read and write
  /// \param function_id: Name of the enclosing function, which temporaries
  ///   are added to
  /// \param source_location: Location of the statement
  /// \param dest: Goto program to append the instructions to
  void operator()(
    const asm_footprintt &footprint,
    const irep_idt &function_id,
    const source_locationt &source_location,
    goto_programt &dest);

  /// Appends to \p dest the expressions contained in \p expr that may hold
  /// addresses, as described for \ref asm_footprintt::addresses.
  static void collect_addresses(
    const exprt &expr,
    const namespacet &ns,
    std::vector<exprt> &dest);

private:
  symbol_table_baset &symbol_table;
};

#endif // CPROVER_ASSEMBLER_ASM_APPROXIMATION_H
