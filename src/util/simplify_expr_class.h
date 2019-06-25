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
#include "type.h"
// #define USE_LOCAL_REPLACE_MAP
#ifdef USE_LOCAL_REPLACE_MAP
#include "replace_expr.h"
#endif

class abs_exprt;
class array_exprt;
class bswap_exprt;
class byte_extract_exprt;
class byte_update_exprt;
class dereference_exprt;
class exprt;
class extractbits_exprt;
class function_application_exprt;
class if_exprt;
class index_exprt;
class member_exprt;
class namespacet;
class popcount_exprt;
class refined_string_exprt;
class tvt;
class typecast_exprt;

#define forall_value_list(it, value_list) \
  for(simplify_exprt::value_listt::const_iterator it=(value_list).begin(); \
      it!=(value_list).end(); ++it)

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

  static resultt<> unchanged(exprt expr)
  {
    return resultt<>(resultt<>::UNCHANGED, std::move(expr));
  }

  static resultt<> changed(resultt<> result)
  {
    result.expr_changed = resultt<>::CHANGED;
    return result;
  }

  // These below all return 'true' if the simplification wasn't applicable.
  // If false is returned, the expression has changed.
  resultt<> simplify_typecast(const typecast_exprt &);
  bool simplify_extractbit(exprt &expr);
  bool simplify_extractbits(extractbits_exprt &expr);
  bool simplify_concatenation(exprt &expr);
  bool simplify_mult(exprt &expr);
  bool simplify_div(exprt &expr);
  bool simplify_mod(exprt &expr);
  bool simplify_plus(exprt &expr);
  bool simplify_minus(exprt &expr);
  bool simplify_floatbv_op(exprt &expr);
  bool simplify_floatbv_typecast(exprt &expr);
  bool simplify_shifts(exprt &expr);
  bool simplify_power(exprt &expr);
  bool simplify_bitwise(exprt &expr);
  bool simplify_if_preorder(if_exprt &expr);
  bool simplify_if(if_exprt &expr);
  bool simplify_bitnot(exprt &expr);
  bool simplify_not(exprt &expr);
  bool simplify_boolean(exprt &expr);
  bool simplify_inequality(exprt &expr);
  bool simplify_ieee_float_relation(exprt &expr);
  bool simplify_lambda(exprt &expr);
  bool simplify_with(exprt &expr);
  bool simplify_update(exprt &expr);
  bool simplify_index(exprt &expr);
  bool simplify_member(exprt &expr);
  resultt<> simplify_byte_update(const byte_update_exprt &);
  resultt<> simplify_byte_extract(const byte_extract_exprt &);
  bool simplify_pointer_object(exprt &expr);
  bool simplify_object_size(exprt &expr);
  bool simplify_dynamic_size(exprt &expr);
  bool simplify_is_dynamic_object(exprt &expr);
  bool simplify_is_invalid_pointer(exprt &expr);
  bool simplify_same_object(exprt &expr);
  bool simplify_good_pointer(exprt &expr);
  bool simplify_object(exprt &expr);
  bool simplify_unary_minus(exprt &expr);
  bool simplify_unary_plus(exprt &expr);
  resultt<> simplify_dereference(const dereference_exprt &);
  bool simplify_address_of(exprt &expr);
  bool simplify_pointer_offset(exprt &expr);
  bool simplify_bswap(bswap_exprt &expr);
  bool simplify_isinf(exprt &expr);
  bool simplify_isnan(exprt &expr);
  bool simplify_isnormal(exprt &expr);
  resultt<> simplify_abs(const abs_exprt &);
  bool simplify_sign(exprt &expr);
  resultt<> simplify_popcount(const popcount_exprt &);
  bool simplify_complex(exprt &expr);

  /// Attempt to simplify mathematical function applications if we have
  /// enough information to do so. Currently focused on constant comparisons.
  resultt<> simplify_function_application(const function_application_exprt &);

  // auxiliary
  bool simplify_if_implies(
    exprt &expr, const exprt &cond, bool truth, bool &new_truth);
  bool simplify_if_recursive(exprt &expr, const exprt &cond, bool truth);
  bool simplify_if_conj(exprt &expr, const exprt &cond);
  bool simplify_if_disj(exprt &expr, const exprt &cond);
  bool simplify_if_branch(exprt &trueexpr, exprt &falseexpr, const exprt &cond);
  bool simplify_if_cond(exprt &expr);
  bool eliminate_common_addends(exprt &op0, exprt &op1);
  static tvt objects_equal(const exprt &a, const exprt &b);
  static tvt objects_equal_address_of(const exprt &a, const exprt &b);
  bool simplify_address_of_arg(exprt &expr);
  bool simplify_inequality_both_constant(exprt &);
  bool simplify_inequality_no_constant(exprt &);
  bool simplify_inequality_rhs_is_constant(exprt &);
  bool simplify_inequality_address_of(exprt &expr);
  bool simplify_inequality_pointer_object(exprt &expr);

  // main recursion
  bool simplify_node(exprt &expr);
  bool simplify_node_preorder(exprt &expr);
  bool simplify_rec(exprt &expr);

  virtual bool simplify(exprt &expr);

  typedef std::set<mp_integer> value_listt;
  bool get_values(const exprt &expr, value_listt &value_list);

  static bool is_bitvector_type(const typet &type)
  {
    return type.id()==ID_unsignedbv ||
           type.id()==ID_signedbv ||
           type.id()==ID_bv;
  }

  // bit-level conversions
  optionalt<exprt>
  bits2expr(const std::string &bits, const typet &type, bool little_endian);

  optionalt<std::string> expr2bits(const exprt &, bool little_endian);

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
