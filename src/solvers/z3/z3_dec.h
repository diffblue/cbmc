/*******************************************************************\

Module:

Author: Lucas Cordeiro, lcc08r@ecs.soton.ac.uk

\*******************************************************************/

#ifndef CPROVER_SOLVERS_Z3_DEC_H
#define CPROVER_SOLVERS_Z3_DEC_H

/*
#include <map>
#include <queue>

#include <hash_cont.h>
*/

#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/pointer_logic.h>

#include "z3_prop.h"

class z3_prop_wrappert
{
public:
  z3_prop_wrappert() { }

protected:
  z3_propt z3_prop;
};

class z3_dect:protected z3_prop_wrappert, public prop_convt
{
public:
  z3_dect();
  ~z3_dect() { }

  /*
  Z3_lbool check2_z3_properties();
  void set_z3_encoding(bool enc);
  void set_z3_ecp(bool ecp);
  */

  // overloading
  virtual exprt get(const exprt &expr) const;

  /*
  u_int get_number_variables_z3(void);
  u_int get_number_vcs_z3(void);
  */

protected:
  #if 0
  virtual literalt convert_rest(const exprt &expr);
  virtual void set_to(const exprt &expr, bool value);
  bool assign_z3_expr(const exprt expr);
  u_int convert_member_name(const exprt &lhs, const exprt &rhs);

  bool create_array_type(const typet &type, Z3_type_ast &bv);
  bool create_type(const typet &type, Z3_type_ast &bv);
  bool create_struct_type(const typet &type, Z3_type_ast &bv);
  bool create_enum_type(const typet &type, Z3_type_ast &bv);
  bool create_pointer_type(const typet &type, Z3_type_ast &bv);
  Z3_ast convert_lt(const exprt &expr);
  Z3_ast convert_gt(const exprt &expr);
  Z3_ast convert_le(const exprt &expr);
  Z3_ast convert_ge(const exprt &expr);
  Z3_ast convert_eq(const exprt &expr);
  Z3_ast convert_invalid(const exprt &expr);
  Z3_ast convert_same_object(const exprt &expr);
  Z3_ast convert_dynamic_object(const exprt &expr);
  Z3_ast convert_overflow_sum(const exprt &expr);
  Z3_ast convert_overflow_sub(const exprt &expr);
  Z3_ast convert_overflow_mul(const exprt &expr);
  Z3_ast convert_overflow_unary(const exprt &expr);
  Z3_ast convert_overflow_typecast(const exprt &expr);
  Z3_ast convert_rest_index(const exprt &expr);
  Z3_ast convert_rest_member(const exprt &expr);
  bool convert_rel(const exprt &expr, Z3_ast &bv);
  bool convert_typecast(const exprt &expr, Z3_ast &bv);
  bool convert_struct(const exprt &expr, Z3_ast &bv);
  bool convert_z3_pointer(const exprt &expr, std::string symbol, Z3_ast &bv);
  bool convert_zero_string(const exprt &expr, Z3_ast &bv);
  bool convert_array(const exprt &expr, Z3_ast &bv);
  bool convert_constant(const exprt &expr, Z3_ast &bv);
  bool convert_bitwise(const exprt &expr, Z3_ast &bv);
  bool convert_unary_minus(const exprt &expr, Z3_ast &bv);
  bool convert_if(const exprt &expr, Z3_ast &bv);
  bool convert_logical_ops(const exprt &expr, Z3_ast &bv);
  bool convert_logical_not(const exprt &expr, Z3_ast &bv);
  bool convert_equality(const exprt &expr, Z3_ast &bv);
  bool convert_add(const exprt &expr, Z3_ast &bv);
  bool convert_sub(const exprt &expr, Z3_ast &bv);
  bool convert_div(const exprt &expr, Z3_ast &bv);
  bool convert_mod(const exprt &expr, Z3_ast &bv);
  bool convert_mul(const exprt &expr, Z3_ast &bv);
  bool convert_pointer(const exprt &expr, Z3_ast &bv);
  bool convert_array_of(const exprt &expr, Z3_ast &bv);
  bool convert_index(const exprt &expr, Z3_ast &bv);
  bool convert_shift(const exprt &expr, Z3_ast &bv);
  bool convert_abs(const exprt &expr, Z3_ast &bv);
  bool convert_with(const exprt &expr, Z3_ast &bv);
  bool convert_bitnot(const exprt &expr, Z3_ast &bv);
  bool convert_object(const exprt &expr, Z3_ast &bv);
  bool select_pointer_offset(const exprt &expr, Z3_ast &bv);
  bool convert_member(const exprt &expr, Z3_ast &bv);
  bool convert_pointer_object(const exprt &expr, Z3_ast &bv);
  bool convert_zero_string_length(const exprt &expr, Z3_ast &bv);
  bool select_pointer_value(Z3_ast object, Z3_ast offset, Z3_ast &bv);
  bool convert_z3_expr(const exprt &expr, Z3_ast &bv);

  bool convert_identifier(const std::string &identifier, const typet &type, Z3_ast &bv);
  bool convert_bv(const exprt &expr, Z3_ast &bv);

  exprt bv_get_rec(
	const Z3_ast &bv,
    std::vector<exprt> &unknown,
    const bool cache,
    const typet &type) const;

  void fill_vector(
    const Z3_ast &bv,
    std::vector<exprt> &unknown,
    const typet &type) const;

  pointer_logict pointer_logic;

  struct eqstr
  {
    bool operator()(const char* s1, const char* s2) const
    {
      return strcmp(s1, s2) == 0;
    }
  };

  typedef hash_map_cont<const exprt, Z3_ast, irep_hash> bv_cachet;
  bv_cachet bv_cache;

  typedef hash_map_cont<const exprt, std::string, irep_hash> z3_cachet;
  z3_cachet z3_cache;

  typedef std::map<std::string, Z3_ast> map_varst;
  map_varst map_vars;

private:
  std::string itos(int i);
  bool is_bv(const typet &type);
  bool check_all_types(const typet &type);
  bool is_ptr(const typet &type);
  bool is_signed(const typet &type);
  bool is_in_cache(const exprt &expr);
  bool write_cache(const exprt &expr);
  const typet select_pointer(const typet &type);
  bool read_cache(const exprt &expr, Z3_ast &bv);
  void create_z3_context(void);
  static std::string ascii2int(char ch);
  void print_data_types(Z3_ast operand0, Z3_ast operand1);
  void print_location(const exprt &expr);
  void show_bv_size(Z3_ast operand);
  Z3_ast convert_number(int value, u_int width, bool type);
  u_int number_variables_z3, set_to_counter, number_vcs_z3;
  z3_capi z3_api;
  bool int_encoding, ignoring_expr, equivalence_checking;
  Z3_context z3_ctx;

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
  #endif
};

#endif
