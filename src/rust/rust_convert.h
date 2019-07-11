/*******************************************************************\

Module: Rust Language Conversion

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language Conversion

#ifndef CPROVER_RUST_RUST_CONVERT_H
#define CPROVER_RUST_RUST_CONVERT_H

class rust_parse_treet;
class message_handlert;
class symbol_tablet;

bool rust_convert(
  const rust_parse_treet &parse_tree,
  symbol_tablet &symbol_table,
  message_handlert &message_handler);

#endif // CPROVER_RUST_RUST_CONVERT_H
