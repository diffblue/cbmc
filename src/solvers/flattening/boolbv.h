/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_SOLVERS_FLATTENING_BOOLBV_H
#define CPROVER_SOLVERS_FLATTENING_BOOLBV_H

//
// convert expression to boolean formula
//

#include <util/byte_operators.h>
#include <util/expr.h>
#include <util/mp_arith.h>
#include <util/optional.h>

#include "bv_utils.h"
#include "boolbv_width.h"
#include "boolbv_map.h"
#include "arrays.h"
#include "functions.h"

class extractbit_exprt;
class extractbits_exprt;
class member_exprt;

class boolbvt:public arrayst
{
public:
  boolbvt(
    const namespacet &_ns,
    propt &_prop):
    arrayst(_ns, _prop),
    unbounded_array(unbounded_arrayt::U_NONE),
    boolbv_width(_ns),
    bv_utils(_prop),
    functions(*this),
    map(_prop, _ns, boolbv_width)
  {
  }

  virtual const bvt &convert_bv( // check cache
    const exprt &expr,
    const optionalt<std::size_t> expected_width = nullopt);

  virtual bvt convert_bitvector(const exprt &expr); // no cache

  // overloading
  exprt get(const exprt &expr) const override;
  void set_to(const exprt &expr, bool value) override;
  void print_assignment(std::ostream &out) const override;

  void clear_cache() override
  {
    SUB::clear_cache();
    bv_cache.clear();
  }

  void post_process() override
  {
    post_process_quantifiers();
    functions.post_process();
    SUB::post_process();
  }

  // get literals for variables/expressions, if available
  virtual bool literal(
    const exprt &expr,
    std::size_t bit,
    literalt &literal) const;

  enum class unbounded_arrayt { U_NONE, U_ALL, U_AUTO };
  unbounded_arrayt unbounded_array;

  mp_integer get_value(const bvt &bv)
  {
    return get_value(bv, 0, bv.size());
  }

  mp_integer get_value(const bvt &bv, std::size_t offset, std::size_t width);

  const boolbv_mapt &get_map() const
  {
    return map;
  }

  boolbv_widtht boolbv_width;

protected:
  bv_utilst bv_utils;

  // uninterpreted functions
  functionst functions;

  // the mapping from identifiers to literals
  boolbv_mapt map;

  // overloading
  literalt convert_rest(const exprt &expr) override;
  virtual bool boolbv_set_equality_to_true(const equal_exprt &expr);

  // NOLINTNEXTLINE(readability/identifiers)
  typedef arrayst SUB;

  void conversion_failed(const exprt &expr, bvt &bv)
  {
    bv=conversion_failed(expr);
  }

  bvt conversion_failed(const exprt &expr);

  typedef std::unordered_map<const exprt, bvt, irep_hash> bv_cachet;
  bv_cachet bv_cache;

  bool type_conversion(
    const typet &src_type, const bvt &src,
    const typet &dest_type, bvt &dest);

  virtual literalt convert_bv_rel(const exprt &expr);
  virtual literalt convert_typecast(const typecast_exprt &expr);
  virtual literalt convert_reduction(const unary_exprt &expr);
  virtual literalt convert_onehot(const unary_exprt &expr);
  virtual literalt convert_extractbit(const extractbit_exprt &expr);
  virtual literalt convert_overflow(const exprt &expr);
  virtual literalt convert_equality(const equal_exprt &expr);
  virtual literalt convert_verilog_case_equality(
    const binary_relation_exprt &expr);
  virtual literalt convert_ieee_float_rel(const exprt &expr);
  virtual literalt convert_quantifier(const exprt &expr);

  virtual bvt convert_index(const exprt &array, const mp_integer &index);
  virtual bvt convert_index(const index_exprt &expr);
  virtual bvt convert_bswap(const bswap_exprt &expr);
  virtual bvt convert_byte_extract(const byte_extract_exprt &expr);
  virtual bvt convert_byte_update(const byte_update_exprt &expr);
  virtual bvt convert_constraint_select_one(const exprt &expr);
  virtual bvt convert_if(const if_exprt &expr);
  virtual bvt convert_struct(const struct_exprt &expr);
  virtual bvt convert_array(const exprt &expr);
  virtual bvt convert_vector(const vector_exprt &expr);
  virtual bvt convert_complex(const complex_exprt &expr);
  virtual bvt convert_complex_real(const complex_real_exprt &expr);
  virtual bvt convert_complex_imag(const complex_imag_exprt &expr);
  virtual bvt convert_lambda(const exprt &expr);
  virtual bvt convert_let(const let_exprt &);
  virtual bvt convert_array_of(const array_of_exprt &expr);
  virtual bvt convert_union(const union_exprt &expr);
  virtual bvt convert_bv_typecast(const typecast_exprt &expr);
  virtual bvt convert_add_sub(const exprt &expr);
  virtual bvt convert_mult(const exprt &expr);
  virtual bvt convert_div(const div_exprt &expr);
  virtual bvt convert_mod(const mod_exprt &expr);
  virtual bvt convert_floatbv_op(const exprt &expr);
  virtual bvt convert_floatbv_typecast(const floatbv_typecast_exprt &expr);
  virtual bvt convert_member(const member_exprt &expr);
  virtual bvt convert_with(const exprt &expr);
  virtual bvt convert_update(const exprt &expr);
  virtual bvt convert_case(const exprt &expr);
  virtual bvt convert_cond(const exprt &expr);
  virtual bvt convert_shift(const binary_exprt &expr);
  virtual bvt convert_bitwise(const exprt &expr);
  virtual bvt convert_unary_minus(const unary_exprt &expr);
  virtual bvt convert_abs(const abs_exprt &expr);
  virtual bvt convert_concatenation(const concatenation_exprt &expr);
  virtual bvt convert_replication(const replication_exprt &expr);
  virtual bvt convert_bv_literals(const exprt &expr);
  virtual bvt convert_constant(const constant_exprt &expr);
  virtual bvt convert_extractbits(const extractbits_exprt &expr);
  virtual bvt convert_symbol(const exprt &expr);
  virtual bvt convert_bv_reduction(const unary_exprt &expr);
  virtual bvt convert_not(const not_exprt &expr);
  virtual bvt convert_power(const binary_exprt &expr);
  virtual bvt convert_function_application(
    const function_application_exprt &expr);

  virtual exprt make_bv_expr(const typet &type, const bvt &bv);
  virtual exprt make_free_bv_expr(const typet &type);

  void convert_with(
    const typet &type,
    const exprt &op1,
    const exprt &op2,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_bv(
    const exprt &op1,
    const exprt &op2,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_array(
    const array_typet &type,
    const exprt &op1,
    const exprt &op2,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_union(
    const union_typet &type,
    const exprt &op2,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_struct(
    const struct_typet &type,
    const exprt &op1,
    const exprt &op2,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_update_rec(
    const exprt::operandst &designator,
    std::size_t d,
    const typet &type,
    std::size_t offset,
    const exprt &new_value,
    bvt &bv);

  virtual exprt bv_get_unbounded_array(const exprt &) const;

  virtual exprt bv_get_rec(
    const bvt &bv,
    const std::vector<bool> &unknown,
    std::size_t offset,
    const typet &type) const;

  exprt bv_get(const bvt &bv, const typet &type) const;
  exprt bv_get_cache(const exprt &expr) const;

  // unbounded arrays
  bool is_unbounded_array(const typet &type) const override;

  // quantifier instantiations
  class quantifiert
  {
  public:
    exprt expr;
    literalt l;
  };

  typedef std::list<quantifiert> quantifier_listt;
  quantifier_listt quantifier_list;

  void post_process_quantifiers();

  typedef std::vector<std::size_t> offset_mapt;
  offset_mapt build_offset_map(const struct_typet &src);

  // strings
  numbering<irep_idt> string_numbering;
};

#endif // CPROVER_SOLVERS_FLATTENING_BOOLBV_H
