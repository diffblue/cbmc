/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_BOOLBV_H
#define CPROVER_BOOLBV_H

//
// convert expression to boolean formula
//

#include <hash_cont.h>
#include <mp_arith.h>
#include <std_types.h>
#include <std_expr.h>

#include <solvers/prop/prop_conv.h>

#include "bv_utils.h"
#include "boolbv_width.h"
#include "boolbv_map.h"
#include "arrays.h"
#include "functions.h"

class boolbvt:public arrayst
{
public:
  boolbvt(
    const namespacet &_ns,
    propt &_prop):
    arrayst(_ns, _prop),
    unbounded_array(U_NONE),
    bv_utils(_prop),
    boolbv_width(_ns),
    functions(*this),
    map(_prop, _ns, boolbv_width)
  {
  }
 
  virtual void convert_bv(const exprt &expr, bvt &bv); // check cache
  virtual void convert_bitvector(const exprt &expr, bvt &bv); // no cache

  // overloading
  virtual exprt get(const exprt &expr) const;
  virtual void set_to(const exprt &expr, bool value);
  virtual void print_assignment(std::ostream &out) const;
  
  virtual void clear_cache()
  {
    SUB::clear_cache();
    bv_cache.clear();
  }

  virtual void post_process()
  {
    post_process_quantifiers();
    functions.post_process();
    SUB::post_process();
  }

  // get literals for variables/expressions, if available
  virtual bool literal(
    const exprt &expr,
    unsigned bit,
    literalt &literal) const;
    
  typedef enum { U_NONE, U_ALL, U_AUTO } unbounded_arrayt;
  unbounded_arrayt unbounded_array;

  mp_integer get_value(const bvt &bv)
  {
    return get_value(bv, 0, bv.size());
  }
  
  mp_integer get_value(const bvt &bv, unsigned offset, unsigned width);
  
  const boolbv_mapt &get_map() const
  {
    return map;
  }

protected:
  bv_utilst bv_utils;
  boolbv_widtht boolbv_width;
  
  // uninterpreted functions
  functionst functions;

  // the mapping from identifiers to literals
  boolbv_mapt map;  
  
  // overloading
  virtual literalt convert_rest(const exprt &expr);
  virtual bool boolbv_set_equality_to_true(const exprt &expr);
  
  typedef arrayst SUB;

  void conversion_failed(const exprt &expr, bvt &bv);

  typedef hash_map_cont<const exprt, bvt, irep_hash> bv_cachet;
  bv_cachet bv_cache;
  
  virtual literalt convert_bv_rel(const exprt &expr);
  virtual literalt convert_typecast(const exprt &expr);
  virtual literalt convert_reduction(const exprt &expr);
  virtual literalt convert_extractbit(const extractbit_exprt &expr);
  virtual literalt convert_overflow(const exprt &expr);
  virtual literalt convert_equality(const class equal_exprt &expr);
  virtual literalt convert_ieee_float_rel(const exprt &expr);
  virtual literalt convert_quantifier(const exprt &expr);

  virtual void convert_index(const exprt &array, const mp_integer &index, bvt &bv);
  virtual void convert_index(const class index_exprt &expr, bvt &bv);
  virtual void convert_byte_extract(
    unsigned width, const exprt &expr,
    const mp_integer &index, bvt &bv, bool little_endian);
  virtual void convert_byte_extract(const exprt &expr, bvt &bv);
  virtual void convert_byte_update(const exprt &expr, bvt &bv);
  virtual void convert_constraint_select_one(const exprt &expr, bvt &bv);
  virtual void convert_if(const exprt &expr, bvt &bv);
  virtual void convert_struct(const exprt &expr, bvt &bv);
  virtual void convert_array(const exprt &expr, bvt &bv);
  virtual void convert_lambda(const exprt &expr, bvt &bv);
  virtual void convert_array_of(const exprt &expr, bvt &bv);
  virtual void convert_union(const exprt &expr, bvt &bv);
  virtual void convert_typecast(const exprt &expr, bvt &bv);
  virtual void convert_add_sub(const exprt &expr, bvt &bv);
  virtual void convert_mult(const exprt &expr, bvt &bv);
  virtual void convert_div(const exprt &expr, bvt &bv);
  virtual void convert_mod(const exprt &expr, bvt &bv);
  virtual void convert_member(const member_exprt &expr, bvt &bv);
  virtual void convert_with(const exprt &expr, bvt &bv);
  virtual void convert_case(const exprt &expr, bvt &bv);
  virtual void convert_cond(const exprt &expr, bvt &bv);
  virtual void convert_shift(const exprt &expr, bvt &bv);
  virtual void convert_bitwise(const exprt &expr, bvt &bv);
  virtual void convert_unary_minus(const exprt &expr, bvt &bv);
  virtual void convert_abs(const exprt &expr, bvt &bv);
  virtual void convert_concatenation(const exprt &expr, bvt &bv);
  virtual void convert_replication(const exprt &expr, bvt &bv);
  virtual void convert_bv_literals(const exprt &expr, bvt &bv);
  virtual void convert_constant(const exprt &expr, bvt &bv);
  virtual void convert_extractbits(const extractbits_exprt &expr, bvt &bv);
  virtual void convert_symbol(const exprt &expr, bvt &bv);

  virtual void make_bv_expr(const typet &type, const bvt &bv, exprt &dest);
  virtual void make_free_bv_expr(const typet &type, exprt &dest);

  void convert_with(
    const typet &type,
    const exprt &op1,
    const exprt &op2,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_bv(
    const typet &type,
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
    const exprt &op1,
    const exprt &op2,
    const bvt &prev_bv,
    bvt &next_bv);

  void convert_with_struct(
    const struct_typet &type,
    const exprt &op1,
    const exprt &op2,
    const bvt &prev_bv,
    bvt &next_bv);

  virtual exprt bv_get_unbounded_array(
    const irep_idt &identifier,
    const class array_typet &type) const;
                    
  virtual exprt bv_get_rec(
    const bvt &bv,
    const std::vector<bool> &unknown,
    unsigned offset,
    const typet &type) const;

  exprt bv_get(const bvt &bv, const typet &type) const;
  exprt bv_get_cache(const exprt &expr) const;
                          
  // unbounded arrays

  bool is_unbounded_array(const typet &type) const;
  
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
  
  typedef std::vector<unsigned> offset_mapt;
  void build_offset_map(const struct_typet &src, offset_mapt &dest);
};

#endif
