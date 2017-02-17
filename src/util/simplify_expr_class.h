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

#include "type.h"
#include "mp_arith.h"
#include "replace_expr.h"

class byte_extract_exprt;
class byte_update_exprt;
class exprt;
class if_exprt;
class index_exprt;
class member_exprt;
class namespacet;
class tvt;

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

  // These below all return 'true' if the simplification wasn't applicable.
  // If false is returned, the expression has changed.

  bool simplify_typecast(exprt &expr);
  bool simplify_extractbit(exprt &expr);
  bool simplify_extractbits(exprt &expr);
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
  bool simplify_byte_update(byte_update_exprt &expr);
  bool simplify_byte_extract(byte_extract_exprt &expr);
  bool simplify_pointer_object(exprt &expr);
  bool simplify_object_size(exprt &expr);
  bool simplify_dynamic_size(exprt &expr);
  bool simplify_dynamic_object(exprt &expr);
  bool simplify_invalid_pointer(exprt &expr);
  bool simplify_same_object(exprt &expr);
  bool simplify_good_pointer(exprt &expr);
  bool simplify_object(exprt &expr);
  bool simplify_unary_minus(exprt &expr);
  bool simplify_unary_plus(exprt &expr);
  bool simplify_dereference(exprt &expr);
  bool simplify_address_of(exprt &expr);
  bool simplify_pointer_offset(exprt &expr);
  bool simplify_bswap(exprt &expr);
  bool simplify_isinf(exprt &expr);
  bool simplify_isnan(exprt &expr);
  bool simplify_isnormal(exprt &expr);
  bool simplify_abs(exprt &expr);
  bool simplify_sign(exprt &expr);
  bool simplify_popcount(exprt &expr);

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
  bool simplify_inequality_constant(exprt &expr);
  bool simplify_inequality_not_constant(exprt &expr);
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
  exprt bits2expr(
    const std::string &bits, const typet &type, bool little_endian);
  std::string expr2bits(const exprt &expr, bool little_endian);

protected:
  const namespacet &ns;
#ifdef DEBUG_ON_DEMAND
  bool debug_on;
#endif
  replace_mapt local_replace_map;
};

#endif // CPROVER_UTIL_SIMPLIFY_EXPR_CLASS_H
