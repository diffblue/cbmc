/*******************************************************************\

Module: Perform Memory-mapped I/O instrumentation

Author: Daniel Kroening

Date:   April 2017

\*******************************************************************/

/// \file
/// Perform Memory-mapped I/O instrumentation
///
/// \details
/// This pass instruments pointer dereferences that target integer addresses
/// (memory-mapped I/O) so that they access modeled objects instead of raw
/// memory.
///
/// Two modes are supported and can be combined:
///
/// **Callback model** (`--mmio`):
/// If a modelling function named `__CPROVER_mm_io_r` exists in the symbol
/// table, this pass inserts calls to it before pointer dereference reads
/// (only when there is a single dereference on the RHS of an assignment).
/// If `__CPROVER_mm_io_w` exists, calls are inserted before all pointer
/// dereference writes (on the LHS of assignments). This enables custom
/// read/write handlers that model device-specific behaviour.
///
/// **Per-region object model** (`--mmio-region addr:size`):
/// Each declared MMIO region becomes an individual byte-array object in the
/// symbol table (named `__CPROVER_mmio_region_0x<addr>`). Reads from
/// addresses within a region are replaced by an `if_exprt` that selects the
/// appropriate array element when the address is an integer address, and
/// falls back to the original dereference otherwise. Writes are replaced by
/// a conditional GOTO dispatch that directs the store to the matching region
/// object. Constant addresses are resolved at instrumentation time; symbolic
/// addresses produce a chain of conditionals over all declared regions.
/// This option is supported by both `cbmc` and `goto-instrument`.
///
/// For details on usage see the "Modeling Memory-mapped I/O" section of the
/// CProver manual (doc/cprover-manual/modeling-mmio.md).

#ifndef CPROVER_GOTO_PROGRAMS_MM_IO_H
#define CPROVER_GOTO_PROGRAMS_MM_IO_H

#include <util/irep.h>
#include <util/mp_arith.h>

#include <list>
#include <string>
#include <vector>

class goto_functionst;
class goto_modelt;
class message_handlert;
class symbol_tablet;

/// Represents a contiguous MMIO region defined via `--mmio-region`.
/// Each region is backed by a byte-array symbol in the symbol table
/// whose name encodes the start address.
struct mmio_regiont
{
  mp_integer start_address; ///< First byte address of the region
  mp_integer size;          ///< Size of the region in bytes
  irep_idt object_name;     ///< Backing array symbol name

  mmio_regiont(
    const mp_integer &_start_address,
    const mp_integer &_size,
    const irep_idt &_object_name)
    : start_address(_start_address), size(_size), object_name(_object_name)
  {
  }
};

/// Instrument MMIO using the callback model
/// (`__CPROVER_mm_io_r` / `__CPROVER_mm_io_w`).
/// Can be combined with the per-region model; in that case the per-region
/// pass should run first so that declared regions get precise modeling.
void mm_io(symbol_tablet &, goto_functionst &, message_handlert &);

/// \copydoc mm_io(symbol_tablet &, goto_functionst &, message_handlert &)
void mm_io(goto_modelt &, message_handlert &);

/// Instrument MMIO using the per-region object model.
/// Each region in \p regions specifies an address range to be backed by a
/// byte-array symbol. The regions must not overlap.
/// \param [in,out] model: the goto model to instrument
/// \param regions: MMIO region specifications
/// \param message_handler: message handler for status and diagnostics
void mm_io(
  goto_modelt &model,
  const std::vector<mmio_regiont> &regions,
  message_handlert &message_handler);

/// Parse `--mmio-region` command-line values into region specifications.
/// Each string must have the format `address:size` (e.g. `0x1000:256`).
/// Hex addresses with `0x`/`0X` prefix are supported.
/// \param region_specs: raw command-line values
/// \param message_handler: for status messages
/// \return parsed and validated regions (checked for overlaps)
/// \throws invalid_command_line_argument_exceptiont on bad format or overlap
std::vector<mmio_regiont> parse_mmio_regions(
  const std::list<std::string> &region_specs,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_MM_IO_H
