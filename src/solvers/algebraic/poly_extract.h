/// \file
/// Extract polynomial equations from CBMC expression trees

#ifndef CPROVER_SOLVERS_ALGEBRAIC_POLY_EXTRACT_H
#define CPROVER_SOLVERS_ALGEBRAIC_POLY_EXTRACT_H

#include <util/expr.h>
#include <util/irep.h>

#include "poly_ring.h"

#include <map>
#include <optional>
#include <vector>

/// Extracts polynomial equations over Z_{2^d} from CBMC expression trees.
/// Expressions involving only +, -, *, constants, and symbols are converted
/// to polynomials. Expressions with bitwise ops, shifts, division, or
/// comparisons are left as residual (non-polynomial) constraints.
class poly_extractort
{
public:
  /// Convert an expression to a polynomial over Z_{2^d}.
  /// Returns nullopt if the expression contains non-polynomial operations.
  std::optional<polynomialt> to_polynomial(const exprt &e);

  /// Given an equality constraint (lhs == rhs), extract the polynomial
  /// equation lhs - rhs = 0. Returns nullopt if either side is
  /// non-polynomial.
  std::optional<polynomialt> extract_equation(const exprt &eq);

  /// Get the variable index for a symbol (creates new index if needed)
  std::size_t get_var_index(const irep_idt &name);

  /// Get the bitwidth for polynomial arithmetic (0 if not yet determined)
  unsigned get_bitwidth() const
  {
    return bitwidth;
  }

  /// Side equations generated when decomposing inline multiplications.
  /// E.g., for mult(a,b), a fresh variable c is introduced and
  /// the equation c - a*b = 0 is added here.
  std::vector<polynomialt> side_equations;

private:
  std::map<irep_idt, std::size_t> var_map;
  std::size_t next_var_index = 0;
  std::size_t next_fresh = 0;
  unsigned bitwidth = 0;

  /// Set bitwidth from a bitvector type. Returns false if incompatible.
  bool set_bitwidth(const typet &type);
};

#endif // CPROVER_SOLVERS_ALGEBRAIC_POLY_EXTRACT_H
