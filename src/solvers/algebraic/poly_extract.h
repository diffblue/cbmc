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

  /// Encode an asserted relational predicate into one or more
  /// polynomial equations (Re 4 sub-goal 6). Currently supports
  /// ID_lt / ID_le with one constant operand:
  ///   - bvult x C, bvule x C: upper bounds on a symbolic x.
  ///   - bvult C x, bvule C x: lower bounds on a symbolic x.
  /// Signed comparisons (bvslt / bvsle) reduce to unsigned via the
  /// standard sign-bit XOR transformation.
  ///
  /// Returns the polynomial equations encoding the predicate's truth.
  /// Returns an empty vector if the predicate is trivially true; the
  /// caller distinguishes "trivially true" from "not handled" via the
  /// optional wrapper (nullopt = not handled, leave to bit-blasting).
  std::optional<std::vector<polynomialt>>
  extract_predicate(const exprt &pred, bool value);

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

  /// Return the host substitutions for linear elimination
  /// (Re 4 sub-goal 3 follow-on). For each host variable h with
  /// bit decomposition [b_0, ..., b_{d-1}], the substitution maps
  /// h -> sum_i 2^i b_i (a polynomial in the bit variables).
  ///
  /// Substituting these into all polynomials of the basis
  /// eliminates the host variables and makes the sum-decomposition
  /// equations trivially zero, drastically reducing the work
  /// Buchberger has to do.
  ///
  /// Also includes any predicate-induced substitutions (Re 4
  /// sub-goal 6): when extract_predicate detects bit positions
  /// forced to a constant (e.g., the high bits of a value
  /// constrained by `bvult x 2^k`), it adds the corresponding
  /// b_i -> 0 substitutions, which propagate the bit constraint
  /// through all polynomials before Buchberger runs.
  std::map<std::size_t, polynomialt> get_host_substitutions() const
  {
    std::map<std::size_t, polynomialt> result;
    if(bitwidth == 0)
      return result;
    for(const auto &[host_idx, bit_indices] : bit_decomp_cache)
    {
      polynomialt sum{bitwidth};
      for(unsigned i = 0; i < bit_indices.size(); ++i)
      {
        polynomialt bit_term{bitwidth, mp_integer{1}, bit_indices[i]};
        mp_integer coeff = power(mp_integer{2}, mp_integer{i});
        sum = sum + bit_term * coeff;
      }
      result.emplace(host_idx, std::move(sum));
    }
    // Predicate-induced substitutions take precedence over host
    // substitutions (the bit variable is the more granular target).
    for(const auto &[var_idx, sub_poly] : additional_substitutions)
      result.insert_or_assign(var_idx, sub_poly);
    return result;
  }

  /// Predicate-induced substitutions populated by extract_predicate.
  /// Each entry maps a polynomial variable index (typically a bit
  /// variable) to a constant polynomial it is forced to equal.
  std::map<std::size_t, polynomialt> additional_substitutions;

  /// Materialise bit-level alignment polynomials for shift identities
  /// (P2: parity-aware reasoning). Scans the supplied polynomial
  /// equations for patterns of the form
  ///
  ///     h - c*x = 0   (or equivalently  c*x - h = 0)
  ///
  /// where h and x are bit-decomposed hosts and c is a constant
  /// power of 2 in [2, 2^{d-1}]. Each match produces:
  ///
  ///     b_{h,i} = 0                  for i in [0, k-1]   (low bits zero)
  ///     b_{h,i+k} = b_{x,i}          for i in [0, d-1-k] (shifted bits)
  ///
  /// where k = log2(c). These linear bit-equalities make the parity
  /// structure of the multiplication explicit, which would otherwise
  /// require Buchberger to deduce position-by-position and is
  /// intractable on shift-related identities of width >= 32 (cf.
  /// the toom-scaled case in §4.6).
  ///
  /// Soundness: in Z_{2^d} the polynomial h - 2^k x = 0 implies bit
  /// b_{h,i} = bit b_{x,i-k} for i >= k and bit b_{h,i} = 0 for
  /// i < k, modulo the Frobenius idempotency of the bit variables.
  /// The alignment equations are valid consequences in the bit-
  /// decomposed model.
  ///
  /// The alignments are written as substitutions
  /// (additional_substitutions) rather than equations: substituting
  /// b_{h, i+k} -> b_{x, i} eagerly through the basis avoids
  /// generating O(d) extra polynomials in Buchberger and exposes the
  /// shift structure during linear elimination.
  ///
  /// Returns the new alignment polynomials. Modifies the extractor's
  /// additional_substitutions for the substitution-based encodings.
  std::vector<polynomialt>
  materialise_bit_alignments(const std::vector<polynomialt> &equations);

private:
  /// Inner implementation of `to_polynomial`. The public entry point
  /// adds memoisation around this; do not call this directly.
  std::optional<polynomialt> to_polynomial_impl(const exprt &e);

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

  /// bvudiv/bvurem polynomial encoding cache (Phase 2). Maps a
  /// canonical (s, t) operand pair to the fresh polynomial-variable
  /// indices `(q_idx, r_idx)` introduced for `bvudiv s t` and
  /// `bvurem s t`. Both operations on the same operands share the
  /// same q, r and the side equation `q*t + r - s = 0` is added
  /// only once.
  ///
  /// Soundness: in any model of the SMT formula, setting
  /// `q := bvudiv s t` and `r := bvurem s t` satisfies the
  /// polynomial equation. When `t = 0` the equation `0 + r - s = 0`
  /// forces `r = s` (matching SMT-LIB-2 `bvurem s 0 = s`) and `q`
  /// is unconstrained at the polynomial level. The polynomial
  /// abstraction is therefore over-approximate (the polynomial
  /// system has more solutions than the SMT formula), which is
  /// sound for UNSAT detection.
  ///
  /// PROOF: formal-proofs/BvDivPolyEncoding.lean::
  ///        bvdiv_polynomial_correct,
  ///        bvdiv_polynomial_overapprox.
  std::map<std::pair<exprt, exprt>, std::pair<std::size_t, std::size_t>>
    bvdiv_qr_cache;

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

  /// to_polynomial result cache. CBMC's exprt uses irept-based
  /// structural sharing, so identical subexpressions can appear
  /// multiple times in a formula DAG. Caching avoids redundant
  /// recursion on shared subexpressions.
  ///
  /// Soundness: the function's side effects (`var_input_widths`
  /// updates) are idempotent ("first wins" via
  /// `find(...) == end()`), so a cache hit need not re-apply them.
  /// The polynomial result is purely a function of the expression.
  std::map<exprt, std::optional<polynomialt>> to_polynomial_cache;

  /// Set bitwidth from a bitvector type. Returns false if incompatible.
  bool set_bitwidth(const typet &type);
};

#endif // CPROVER_SOLVERS_ALGEBRAIC_POLY_EXTRACT_H
