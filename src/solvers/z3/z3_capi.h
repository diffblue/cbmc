/*******************************************************************\

Module:

Author:

\*******************************************************************/

#ifndef CPROVER_SOLVERS_Z3_CAPI_H
#define CPROVER_SOLVERS_Z3_CAPI_H

class z3_capi
{
public:
  z3_capi();  // constructor
  ~z3_capi(); // destructor

  #if 0
  Z3_context mk_context();
  Z3_ast mk_var(Z3_context ctx, const char * name, Z3_type_ast ty);
  Z3_ast mk_bool_var(Z3_context ctx, const char * name);
  Z3_ast mk_int_var(Z3_context ctx, const char * name);
  Z3_ast mk_int(Z3_context ctx, int v);
  Z3_ast mk_unsigned_int(Z3_context ctx, unsigned int v);
  Z3_ast mk_real_var(Z3_context ctx, const char * name);
  Z3_ast mk_unary_app(Z3_context ctx, Z3_const_decl_ast f, Z3_ast x);
  Z3_ast mk_binary_app(Z3_context ctx, Z3_const_decl_ast f, Z3_ast x, Z3_ast y);
  Z3_lbool check(Z3_context ctx, Z3_lbool expected_result);
  Z3_lbool check2(Z3_context ctx, Z3_lbool expected_result);
  void prove(Z3_context ctx, Z3_ast f, Z3_bool is_valid);
  void assert_inj_axiom(Z3_context ctx, Z3_const_decl_ast f, unsigned i);
  void display_sort(Z3_context c, FILE * out, Z3_sort ty);
  void assert_comm_axiom(Z3_context ctx, Z3_const_decl_ast f);
  void display_ast(Z3_context c, FILE * out, Z3_ast v);
  Z3_ast mk_tuple_update(Z3_context c, Z3_ast t, unsigned i, Z3_ast new_val);
  Z3_ast mk_tuple_select(Z3_context c, Z3_ast t, unsigned i);
  void display_symbol(Z3_context c, FILE * out, Z3_symbol s);
  void display_type(Z3_context c, FILE * out, Z3_type_ast ty);
  void display_function_interpretations(Z3_context c, FILE * out, Z3_model m);
  void display_model(Z3_context c, FILE * out, Z3_model m);
  void display_version();

private:
  Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err);
  Z3_context z3_ctx;
  #endif
};

#endif
