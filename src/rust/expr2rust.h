/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#ifndef CPROVER_RUST_EXPR2RUST_H
#define CPROVER_RUST_EXPR2RUST_H

#include <string>

class exprt;
class namespacet;
class typet;

std::string expr2rust(const exprt &expr, const namespacet &ns);
std::string type2rust(const typet &type, const namespacet &ns);

#endif // CPROVER_RUST_EXPR2RUST_H
