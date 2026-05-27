/// \file
/// Extract polynomial equations from CBMC expression trees

#ifndef CPROVER_SOLVERS_ALGEBRAIC_POLY_EXTRACT_H
#define CPROVER_SOLVERS_ALGEBRAIC_POLY_EXTRACT_H

#include <util/expr.h>
#include <util/irep.h>

#include "poly_ring.h"

#include <map>
#include <optional>
#include <set>
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

  /// Decompose an expression into its bit variables, soundly.
  ///
  /// Returns a vector of polynomials [b_0, ..., b_{d-1}], where each
  /// b_i is a polynomial of the form (1 * x_v) for a fresh bit
  /// variable v_i. Side equations are added to enforce:
  ///   - idempotency: b_i^2 - b_i = 0 (forces b_i in {0, 1})
  ///   - sum-decomposition: e - sum_i 2^i b_i = 0
  ///
  /// In Z_{2^d}, idempotency b(b - 1) = 0 implies b = 0 or b = 1
  /// (since b and b - 1 are coprime, one must be 0 mod 2^d). Combined
  /// with sum-decomposition, the b_i are uniquely the bits of e.
  ///
  /// Caches per host-variable index so repeated decompositions of
  /// the same variable reuse the same bit variables (and side
  /// equations are added only once).
  ///
  /// Returns nullopt if e is non-polynomial or has unsupported type.
  std::optional<std::vector<polynomialt>> decompose_bits(const exprt &e);

  /// Given an equality constraint (lhs == rhs), extract the polynomial
  /// equation lhs - rhs = 0. Returns nullopt if either side is
  /// non-polynomial.
  std::optional<polynomialt> extract_equation(const exprt &eq);

  /// Get the variable index for a symbol (creates new index if needed)
  std::size_t get_var_index(const irep_idt &name);

  /// Get the reverse mapping: polynomial variable index → symbol name
  const std::map<std::size_t, irep_idt> &get_reverse_var_map() const
  {
    return reverse_var_map;
  }

  /// Get the bitwidth for polynomial arithmetic (0 if not yet determined)
  unsigned get_bitwidth() const
  {
    return bitwidth;
  }

  /// Side equations generated when decomposing inline multiplications.
  /// E.g., for mult(a,b), a fresh variable c is introduced and
  /// the equation c - a*b = 0 is added here.
  std::vector<polynomialt> side_equations;

  /// When true, inline all products instead of creating fresh variables.
  /// Used by the vanishing polynomial test which needs a single polynomial.
  bool inline_products = false;

  /// Map from variable index to actual input bitwidth (may be smaller
  /// than the polynomial bitwidth due to zero_extend).
  std::map<std::size_t, unsigned> var_input_widths;

  /// Return the set of polynomial variable indices that are bit
  /// variables introduced by decompose_bits(). Used to enable
  /// Frobenius-aware reduction in the Gröbner basis solver
  /// (Re 4 sub-goal 3): bit variables satisfy b^2 = b in Z_{2^d},
  /// so all higher powers reduce to b.
  std::set<std::size_t> get_bit_var_indices() const
  {
    std::set<std::size_t> result;
    for(const auto &[host_idx, bit_indices] : bit_decomp_cache)
    {
      for(std::size_t b_idx : bit_indices)
        result.insert(b_idx);
    }
    return result;
  }

private:
  std::map<irep_idt, std::size_t> var_map;
  std::map<std::size_t, irep_idt> reverse_var_map;
  std::size_t next_var_index = 0;
  std::size_t next_fresh = 0;
  unsigned bitwidth = 0;

  /// Bit-decomposition cache: maps host variable index to the vector
  /// of bit-variable indices [v_0, ..., v_{d-1}] for that host.
  /// Each polynomial variable that gets bit-decomposed is decomposed
  /// at most once per extractor instance; subsequent decompose_bits
  /// calls return polynomials wrapping the cached bit variables.
  std::map<std::size_t, std::vector<std::size_t>> bit_decomp_cache;

  /// Polynomial-form → host variable index cache. When
  /// decompose_bits is called on a compound expression that
  /// reduces to a polynomial that has been seen before (e.g.,
  /// (a+b) and (b+a) both normalise to the same polynomial), we
  /// reuse the same host variable rather than introducing a fresh
  /// one. This avoids duplicating bit decompositions across
  /// syntactically-different-but-semantically-equal polynomials.
  ///
  /// Key: a canonical string serialisation of the polynomial's
  /// (term, monomial) sequence. Polynomials are normalised
  /// before serialisation so that the key is order-invariant.
  std::map<std::string, std::size_t> poly_host_cache;

  /// Set bitwidth from a bitvector type. Returns false if incompatible.
  bool set_bitwidth(const typet &type);
};

#endif // CPROVER_SOLVERS_ALGEBRAIC_POLY_EXTRACT_H
