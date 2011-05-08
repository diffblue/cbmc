/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#ifndef CPROVER_PROP_BOOLECTOR_DEC_H
#define CPROVER_PROP_BOOLECTOR_DEC_H

#include <hash_cont.h>

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/pointer_logic.h>

#include "boolector_prop.h"

class boolector_prop_wrappert
{
public:
  boolector_prop_wrappert() { }

protected:
  boolector_propt boolector_prop;
};

class boolector_dect:protected boolector_prop_wrappert, public prop_convt
{
public:
  boolector_dect();

  ~boolector_dect()
  {
  }

  unsigned int get_number_variables_boolector();
  int check_boolector_properties();
  // overloading
  virtual decision_proceduret::resultt dec_solve();
  // overloading
  virtual exprt get(const exprt &expr) const;

protected:
  virtual literalt convert_rest(const exprt &expr);
  virtual void set_to(const exprt &expr, bool value);

  bool assign_boolector_expr(const exprt expr);
  class BtorExp *convert_boolector_expr(const exprt &expr);
  class BtorExp *convert_rel(const exprt &expr);
  class BtorExp *convert_typecast(const exprt &expr);
  class BtorExp *convert_struct(const exprt &expr);
  class BtorExp *convert_union(const exprt &expr);
  class BtorExp *convert_constant(const exprt &expr);
  class BtorExp *convert_concatenation(const exprt &expr);
  class BtorExp *convert_bitwise(const exprt &expr);
  class BtorExp *convert_bitnot(const exprt &expr);
  class BtorExp *convert_unary_minus(const exprt &expr);
  class BtorExp *convert_if(const exprt &expr);
  class BtorExp *convert_logical_ops(const exprt &expr);
  class BtorExp *convert_logical_not(const exprt &expr);
  class BtorExp *convert_equality(const exprt &expr);
  class BtorExp *convert_add(const exprt &expr);
  class BtorExp *convert_sub(const exprt &expr);
  class BtorExp *convert_div(const exprt &expr);
  class BtorExp *convert_mod(const exprt &expr);
  class BtorExp *convert_mul(const exprt &expr);
  class BtorExp *convert_pointer(const exprt &expr);
  class BtorExp *convert_array_of(const exprt &expr);
  class BtorExp *convert_array_of_array(const std::string identifier, const exprt &expr);
  class BtorExp *convert_index(const exprt &expr);
  class BtorExp *convert_shift(const exprt &expr);
  class BtorExp *convert_with(const exprt &expr);
  class BtorExp *convert_extractbit(const exprt &expr);
  class BtorExp *convert_member(const exprt &expr);
  unsigned int convert_member_name(const exprt &lhs, const exprt &rhs);
  class BtorExp *convert_object(const exprt &expr);
  class BtorExp *select_pointer_offset(const exprt &expr);
  class BtorExp *convert_invalid_pointer(const exprt &expr);
  class BtorExp *convert_pointer_object(const exprt &expr);
  class BtorExp *convert_zero_string(const exprt &expr);
  class BtorExp *convert_overflow_sum(const exprt &expr);
  class BtorExp *convert_overflow_sub(const exprt &expr);
  class BtorExp *convert_overflow_mul(const exprt &expr);
  class BtorExp *convert_overflow_typecast(const exprt &expr);
  class BtorExp *convert_overflow_unary(const exprt &expr);
  class BtorExp *convert_boolector_pointer(const exprt &expr);
  class BtorExp *convert_array(const exprt &expr);
  class BtorExp *select_pointer_value(class BtorExp *object, class BtorExp *offset);
  class BtorExp *convert_abs(const exprt &expr);
  class BtorExp *convert_pointer_offset(unsigned bits);

  pointer_logict pointer_logic;

  typedef hash_map_cont<const exprt, std::string, irep_hash> pointer_cachet;
  pointer_cachet pointer_cache;

  typedef hash_map_cont<const exprt, BtorExp*, irep_hash> bv_cachet;
  bv_cachet bv_cache;

  exprt bv_get_rec(
    class BtorExp *bv,
    std::vector<exprt> &unknown,
    const bool cache,
    const typet &type) const;

  resultt read_boolector_result();
  void read_assert(std::istream &in, std::string &line);

private:
  bool is_ptr(const typet &type);
  bool check_all_types(const typet &type);
  bool is_signed(const typet &type);
  bool is_set();
  void write_cache(const exprt &expr);
  class BtorExp *convert_constant_array(const exprt &expr);
  class BtorExp *convert_bv(const exprt &expr);
  class BtorExp *convert_shift_constant(const exprt &expr);
  class BtorExp *create_boolector_array(const typet &type, std::string identifier);
  class BtorExp *read_cache(const exprt &expr);
  class BtorExp *convert_eq(const exprt &expr);
  class BtorExp *convert_ge(const exprt &expr);
  class BtorExp *convert_le(const exprt &expr);
  class BtorExp *convert_gt(const exprt &expr);
  class BtorExp *convert_lt(const exprt &expr);
  class BtorExp *convert_dynamic_object(const exprt &expr);
  class BtorExp *convert_same_object(const exprt &expr);
  class BtorExp *convert_invalid(const exprt &expr);
  void create_boolector_context();
  class BtorExp *convert_identifier(const std::string &identifier, const typet &type);
  void print_data_types(class BtorExp *operand0, class BtorExp *operand1);
  int literal_flag;
  unsigned int number_variables_boolector, set_to_counter, variable_number;
  Btor *boolector_ctx;

  struct identifiert
  {
    typet type;
    exprt value;

    identifiert()
    {
      type.make_nil();
      value.make_nil();
    }
  };

  typedef hash_map_cont<irep_idt, identifiert, irep_id_hash>
    identifier_mapt;

  identifier_mapt identifier_map;
};

#endif
