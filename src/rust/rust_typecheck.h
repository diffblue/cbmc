/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/

/// \file
/// Rust Language

#ifndef CPROVER_RUST_RUST_TYPECHECK_H
#define CPROVER_RUST_RUST_TYPECHECK_H

#include <unordered_set>

#include <util/namespace.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>
#include <util/typecheck.h>

class symbol_exprt;
class codet;

bool rust_typecheck(
  symbol_tablet &symbol_table,
  message_handlert &message_handler);

bool rust_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns);

class rust_typecheckt : public typecheckt
{
public:
  rust_typecheckt(
    symbol_table_baset &_symbol_table,
    message_handlert &_message_handler)
    : typecheckt(_message_handler),
      symbol_table(_symbol_table),
      ns(symbol_table),
      proc_name()
  {
  }

  virtual ~rust_typecheckt()
  {
  }

  virtual void typecheck();
  virtual void typecheck_expr(exprt &expr);

protected:
  symbol_table_baset &symbol_table;
  const namespacet ns;

  // prefix to variables which is set in typecheck_declaration
  irep_idt proc_name;

  void typecheck_expr_or_code(exprt &expr);
  void update_expr_type(exprt &expr, const typet &type);
  void make_type_compatible(exprt &expr, const typet &type, bool must);
  void typecheck_type_symbol(symbolt &)
  {
  }
  void typecheck_non_type_symbol(symbolt &symbol);
  void typecheck_symbol_expr(symbol_exprt &symbol_expr);
  void typecheck_decl(codet &code_decl);
  void typecheck_decl_block(codet &code_decl);
  void typecheck_expr_side_effect(side_effect_exprt &expr);
  void typecheck_expr_address_of(address_of_exprt &expr);
  void typecheck_expr_dereference(dereference_exprt &expr);
  void typecheck_expr_delete(exprt &expr);
  void typecheck_expr_index(exprt &expr);
  void typecheck_expr_proto_field(exprt &expr);
  void typecheck_expr_proto_obj(exprt &expr);
  void typecheck_expr_has_field(exprt &expr);
  void typecheck_expr_ref(exprt &expr);
  void typecheck_expr_field(exprt &expr);
  void typecheck_expr_base(exprt &expr);
  void typecheck_expr_constant(exprt &expr);
  void typecheck_expr_concatenation(exprt &expr);
  void typecheck_expr_subtype(exprt &expr);
  void typecheck_expr_binary_boolean(exprt &expr);
  void typecheck_expr_binary_arith(exprt &expr);
  void typecheck_exp_binary_equal(exprt &expr);
  void typecheck_expr_binary_compare(exprt &expr);
  void typecheck_expr_unary_boolean(exprt &expr);
  void typecheck_expr_unary_string(exprt &expr);
  void typecheck_expr_unary_num(exprt &expr);
  void typecheck_expr_operands(exprt &expr);
  void typecheck_expr_main(exprt &expr);
  void typecheck_code(codet &code);
  void typecheck_function_call(side_effect_exprt &function_call);
  void typecheck_return(code_returnt &code);
  void typecheck_block(codet &code);
  void typecheck_ifthenelse(code_ifthenelset &code);
  void typecheck_assign(code_assignt &code);
  void typecheck_try_catch(code_try_catcht &code);
  void typecheck_type(typet &type);
  void typecheck_loop(codet &code);
  irep_idt add_prefix(const irep_idt &ds);
  irep_idt add_prefix(const irep_idt &ds, int scope_level);
  irep_idt strip_to_base_name(const irep_idt &original);

  typet rust_reconcile_types(exprt &a, exprt &b);

  // overload to use language-specific syntax
  virtual std::string to_string(const exprt &expr);
  virtual std::string to_string(const typet &type);

  // pair is <map of variables, scope level>
  std::vector<std::pair<std::unordered_map<irep_idt, typet>, int>>
    known_symbols;
  std::vector<int> scope_history;
  int max_scope = 0;

  typet lookup_type(exprt &expr);
  typet search_known_symbols(irep_idt const &symbol_name);
  irep_idt find_existing_decorated_symbol(irep_idt const &symbol_name);
};

#endif // CPROVER_RUST_RUST_TYPECHECK_H
