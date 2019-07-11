/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#ifndef CPROVER_RUST_RUST_ENTRY_POINT_H
#define CPROVER_RUST_RUST_ENTRY_POINT_H

class message_handlert;
class symbol_tablet;

bool rust_entry_point(
  class symbol_tablet &symbol_table,
  class message_handlert &message_handler);

#endif // CPROVER_RUST_RUST_ENTRY_POINT_H
