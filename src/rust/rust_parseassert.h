/*******************************************************************\

Module: Rust Language Conversion

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/

/// \file
/// Rust Language Conversion

#ifndef CPROVER_RUST_RUST_PARSEASSERT_H
#define CPROVER_RUST_RUST_PARSEASSERT_H

#include "rust_parser.h"

exprt parse_token_tree(multi_ary_exprt const &tokenTree);

#endif // CPROVER_RUST_RUST_PARSEASSERT_H
