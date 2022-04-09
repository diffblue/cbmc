/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_SIMPLIFY_EXPR_CLASS_H
#define CPROVER_UTIL_SIMPLIFY_EXPR_CLASS_H

// #define DEBUG_ON_DEMAND
#ifdef DEBUG_ON_DEMAND
#include <sys/stat.h>
#endif

#include <set>

#include "expr.h"
#include "mp_arith.h"
#include "nodiscard.h"
#include "type.h"
// #define USE_LOCAL_REPLACE_MAP
#ifdef USE_LOCAL_REPLACE_MAP
#include "replace_expr.h"
#endif

class abs_exprt;
class address_of_exprt;
class array_exprt;
class binary_exprt;
class binary_overflow_exprt;
class binary_relation_exprt;
class bitnot_exprt;
class bitreverse_exprt;
class bswap_exprt;
class byte_extract_exprt;
class byte_update_exprt;
class concatenation_exprt;
class count_leading_zeros_exprt;
class count_trailing_zeros_exprt;
class dereference_exprt;
class div_exprt;
class exprt;
class extractbit_exprt;
class extractbits_exprt;
class floatbv_typecast_exprt;
class function_application_exprt;
class ieee_float_op_exprt;
class if_exprt;
class index_exprt;
class lambda_exprt;
class member_exprt;
class minus_exprt;
class mod_exprt;
class multi_ary_exprt;
class mult_exprt;
class namespacet;
class not_exprt;
class plus_exprt;
class pointer_offset_exprt;
class popcount_exprt;
class refined_string_exprt;
class shift_exprt;
class sign_exprt;
class typecast_exprt;
class unary_exprt;
class unary_minus_exprt;
class unary_overflow_exprt;
class unary_plus_exprt;
class update_exprt;
class with_exprt;

class simplify_exprt
{
public:
  explicit simplify_exprt(const namespacet &_ns):
    do_simplify_if(true),
    ns(_ns)
#ifdef DEBUG_ON_DEMAND
    , debug_on(false)
#endif
  {
#ifdef DEBUG_ON_DEMAND
    struct stat f;
    debug_on=stat("SIMP_DEBUG", &f)==0;
#endif
  }

  virtual ~simplify_exprt()
  {
  }

  bool do_simplify_if;

  template <typename T = exprt>
  struct resultt
  {
    bool has_changed() const
    {
      return expr_changed == CHANGED;
    }

    enum expr_changedt
    {
      CHANGED,
      UNCHANGED
    } expr_changed;

    T expr;

    /// conversion to expression, to enable chaining
    operator T() const
    {
      return expr;
    }

    /// conversion from expression, thus not 'explicit'
    /// marks the expression as "CHANGED"
    // NOLINTNEXTLINE(runtime/explicit)
    resultt(T _expr) : expr_changed(CHANGED), expr(std::move(_expr))
    {
    }

    resultt(expr_changedt _expr_changed, T _expr)
      : expr_changed(_expr_changed), expr(std::move(_expr))
    {
    }
  };

  NODISCARD static resultt<> unchanged(exprt expr)
  {
    return resultt<>(resultt<>::UNCHANGED, std::move(expr));
  }

  NODISCARD static resultt<> changed(resultt<> result)
  {
    result.expr_changed = resultt<>::CHANGED;
    return result;
  }

  // These below all return 'true' if the simplification wasn't applicable.
  // If false is returned, the expression has changed.
  NODISCARD resultt<> simplify_typecast(const typecast_exprt &);
  NODISCARD resultt<> simplify_extractbit(const extractbit_exprt &);
  NODISCARD resultt<> simplify_extractbits(const extractbits_exprt &);
  NODISCARD resultt<> simplify_concatenation(const concatenation_exprt &);
  NODISCARD resultt<> simplify_mult(const mult_exprt &);
  NODISCARD resultt<> simplify_div(const div_exprt &);
  NODISCARD resultt<> simplify_mod(const mod_exprt &);
  NODISCARD resultt<> simplify_plus(const plus_exprt &);
  NODISCARD resultt<> simplify_minus(const minus_exprt &);
  NODISCARD resultt<> simplify_floatbv_op(const ieee_float_op_exprt &);
  NODISCARD resultt<> simplify_floatbv_typecast(const floatbv_typecast_exprt &);
  NODISCARD resultt<> simplify_shifts(const shift_exprt &);
  NODISCARD resultt<> simplify_power(const binary_exprt &);
  NODISCARD resultt<> simplify_bitwise(const multi_ary_exprt &);
  bool simplify_if_preorder(if_exprt &expr);
  NODISCARD resultt<> simplify_if(const if_exprt &);
  NODISCARD resultt<> simplify_bitnot(const bitnot_exprt &);
  NODISCARD resultt<> simplify_not(const not_exprt &);
  NODISCARD resultt<> simplify_boolean(const exprt &);
  NODISCARD resultt<> simplify_inequality(const binary_relation_exprt &);
  NODISCARD resultt<>
  simplify_ieee_float_relation(const binary_relation_exprt &);
  NODISCARD resultt<> simplify_lambda(const lambda_exprt &);
  NODISCARD resultt<> simplify_with(const with_exprt &);
  NODISCARD resultt<> simplify_update(const update_exprt &);
  NODISCARD resultt<> simplify_index(const index_exprt &);
  NODISCARD resultt<> simplify_member(const member_exprt &);
  NODISCARD resultt<> simplify_byte_update(const byte_update_exprt &);
  NODISCARD resultt<> simplify_byte_extract(const byte_extract_exprt &);
  NODISCARD resultt<> simplify_pointer_object(const unary_exprt &);
  NODISCARD resultt<> simplify_object_size(const unary_exprt &);
  NODISCARD resultt<> simplify_is_dynamic_object(const unary_exprt &);
  NODISCARD resultt<> simplify_is_invalid_pointer(const unary_exprt &);
  NODISCARD resultt<> simplify_good_pointer(const unary_exprt &);
  NODISCARD resultt<> simplify_object(const exprt &);
  NODISCARD resultt<> simplify_unary_minus(const unary_minus_exprt &);
  NODISCARD resultt<> simplify_unary_plus(const unary_plus_exprt &);
  NODISCARD resultt<> simplify_dereference(const dereference_exprt &);
  NODISCARD resultt<> simplify_address_of(const address_of_exprt &);
  NODISCARD resultt<> simplify_pointer_offset(const pointer_offset_exprt &);
  NODISCARD resultt<> simplify_bswap(const bswap_exprt &);
  NODISCARD resultt<> simplify_isinf(const unary_exprt &);
  NODISCARD resultt<> simplify_isnan(const unary_exprt &);
  NODISCARD resultt<> simplify_isnormal(const unary_exprt &);
  NODISCARD resultt<> simplify_abs(const abs_exprt &);
  NODISCARD resultt<> simplify_sign(const sign_exprt &);
  NODISCARD resultt<> simplify_popcount(const popcount_exprt &);
  NODISCARD resultt<> simplify_complex(const unary_exprt &);

  /// Try to simplify overflow-+, overflow-*, overflow--, overflow-shl.
  /// Simplification will be possible when the operands are constants or the
  /// types of the operands have infinite domains.
  NODISCARD resultt<> simplify_overflow_binary(const binary_overflow_exprt &);

  /// Try to simplify overflow-unary-.
  /// Simplification will be possible when the operand is constants or the
  /// type of the operand has an infinite domain.
  NODISCARD resultt<> simplify_overflow_unary(const unary_overflow_exprt &);

  /// Attempt to simplify mathematical function applications if we have
  /// enough information to do so. Currently focused on constant comparisons.
  NODISCARD resultt<>
  simplify_function_application(const function_application_exprt &);

  /// Try to simplify count-leading-zeros to a constant expression.
  NODISCARD resultt<> simplify_clz(const count_leading_zeros_exprt &);

  /// Try to simplify count-trailing-zeros to a constant expression.
  NODISCARD resultt<> simplify_ctz(const count_trailing_zeros_exprt &);

  /// Try to simplify bit-reversing to a constant expression.
  NODISCARD resultt<> simplify_bitreverse(const bitreverse_exprt &);

  // auxiliary
  bool simplify_if_implies(
    exprt &expr, const exprt &cond, bool truth, bool &new_truth);
  bool simplify_if_recursive(exprt &expr, const exprt &cond, bool truth);
  bool simplify_if_conj(exprt &expr, const exprt &cond);
  bool simplify_if_disj(exprt &expr, const exprt &cond);
  bool simplify_if_branch(exprt &trueexpr, exprt &falseexpr, const exprt &cond);
  bool simplify_if_cond(exprt &expr);
  NODISCARD resultt<> simplify_address_of_arg(const exprt &);
  NODISCARD resultt<>
  simplify_inequality_both_constant(const binary_relation_exprt &);
  NODISCARD resultt<>
  simplify_inequality_no_constant(const binary_relation_exprt &);
  NODISCARD resultt<>
  simplify_inequality_rhs_is_constant(const binary_relation_exprt &);
  NODISCARD resultt<>
  simplify_inequality_address_of(const binary_relation_exprt &);
  NODISCARD resultt<>
  simplify_inequality_pointer_object(const binary_relation_exprt &);

  // main recursion
  NODISCARD resultt<> simplify_node(exprt);
  bool simplify_node_preorder(exprt &expr);
  NODISCARD resultt<> simplify_rec(const exprt &);

  virtual bool simplify(exprt &expr);

  static bool is_bitvector_type(const typet &type)
  {
    return type.id()==ID_unsignedbv ||
           type.id()==ID_signedbv ||
           type.id()==ID_bv;
  }

protected:
  const namespacet &ns;
#ifdef DEBUG_ON_DEMAND
  bool debug_on;
#endif
#ifdef USE_LOCAL_REPLACE_MAP
  replace_mapt local_replace_map;
#endif

};

#endif // CPROVER_UTIL_SIMPLIFY_EXPR_CLASS_H
