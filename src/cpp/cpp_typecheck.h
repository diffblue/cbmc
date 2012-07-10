/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TYPECHECK_H
#define CPROVER_CPP_TYPECHECK_H

#include <assert.h>

#include <set>
#include <list>
#include <map>

#include <std_code.h>
#include <std_types.h>

#include <ansi-c/c_typecheck_base.h>

#include "cpp_parse_tree.h"
#include "cpp_scopes.h"
#include "cpp_typecheck_resolve.h"
#include "template_map.h"
#include "cpp_member_spec.h"
#include "cpp_template_type.h"
#include "cpp_util.h"

bool cpp_typecheck(
  cpp_parse_treet &cpp_parse_tree,
  contextt &context,
  const std::string &module,
  message_handlert &message_handler);

bool cpp_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns);

class cpp_typecheckt:public c_typecheck_baset
{
public:
  cpp_typecheckt(
    cpp_parse_treet &_cpp_parse_tree,
    contextt &_context,
    const std::string &_module,
    message_handlert &message_handler):
    c_typecheck_baset(_context, _module, message_handler),
    cpp_parse_tree(_cpp_parse_tree),
    template_counter(0),
    anon_counter(0),
    disable_access_control(false)
  {
  }

  cpp_typecheckt(
    cpp_parse_treet &_cpp_parse_tree,
    contextt &_context1,
    const contextt &_context2,
    const std::string &_module,
    message_handlert &message_handler):
    c_typecheck_baset(_context1, _context2,
                      _module, message_handler),
    cpp_parse_tree(_cpp_parse_tree),
    template_counter(0),
    anon_counter(0),
    disable_access_control(false)
  {
  }

  virtual ~cpp_typecheckt() { }

  virtual void typecheck();

  // overload to use C++ syntax

  virtual std::string to_string(const typet &type);
  virtual std::string to_string(const exprt &expr);

  friend class cpp_typecheck_resolvet;
  friend class cpp_declarator_convertert;

  exprt resolve(
    const cpp_namet &cpp_name,
    const cpp_typecheck_resolvet::wantt want,
    const cpp_typecheck_fargst &fargs,
    bool fail_with_exception=true)
  {
    cpp_typecheck_resolvet cpp_typecheck_resolve(*this);
    return cpp_typecheck_resolve.resolve(
      cpp_name, want, fargs, fail_with_exception);
  }

  virtual void typecheck_expr(exprt &expr);

  bool cpp_is_pod(const typet &type) const;

  codet cpp_constructor(
    const locationt &location,
    const exprt &object,
    const exprt::operandst &operands);

protected:
  cpp_scopest cpp_scopes;

  cpp_parse_treet &cpp_parse_tree;
  irep_idt current_linkage_spec;

  void convert(cpp_linkage_spect &);
  void convert(cpp_namespace_spect &);
  void convert(cpp_usingt &);
  void convert(cpp_itemt &);
  void convert(cpp_declarationt &);
  void convert(cpp_declaratort &);

  void convert_initializer(symbolt &symbol);
  void convert_function(symbolt &symbol);

  void convert_pmop(exprt& expr);

  void convert_anonymous_union(
    cpp_declarationt &declaration,
    codet &new_code);

  void convert_anon_struct_union_member(
    const cpp_declarationt &declaration,
    const irep_idt &access,
    struct_typet::componentst &components);

  //
  // Templates
  //
  void salvage_default_parameters(
    const template_typet &old_type,
    template_typet &new_type);

  void check_template_restrictions(
    const irept &cpp_name,
    const irep_idt &final_identifier,
    const typet &final_type);

  void convert_template_declaration(cpp_declarationt &declaration);

  void convert_non_template_declaration(cpp_declarationt &declaration);

  void convert_template_function_or_member_specialization(
    cpp_declarationt &declaration);

  void convert_class_template_specialization(
    cpp_declarationt &declaration);

  void typecheck_class_template(cpp_declarationt &declaration);

  void typecheck_function_template(cpp_declarationt &declaration);

  void typecheck_class_template_member(cpp_declarationt &declaration);

  std::string class_template_identifier(
    const irep_idt &base_name,
    const template_typet &template_type,
    const cpp_template_args_non_tct &partial_specialization_args);
    
  std::string function_template_identifier(
    const irep_idt &base_name,
    const template_typet &template_type,
    const typet &function_type);

  cpp_template_args_tct typecheck_template_args(
    const locationt &location,
    const symbolt &template_symbol,
    const cpp_template_args_non_tct &template_args);
    
  class instantiationt
  {
  public:
    locationt location;
    irep_idt identifier;
    cpp_template_args_tct full_template_args;
  };

  typedef std::list<instantiationt> instantiation_stackt;
  instantiation_stackt instantiation_stack;
  
  void show_instantiation_stack(std::ostream &);
  
  class instantiation_levelt
  {
  public:
    instantiation_levelt(
      instantiation_stackt &_instantiation_stack):
      instantiation_stack(_instantiation_stack)
    {
      instantiation_stack.push_back(instantiationt());
    }
    
    ~instantiation_levelt()
    {
      instantiation_stack.pop_back();
    }
    
  private:
    instantiation_stackt &instantiation_stack;
  };
  
  const symbolt &class_template_symbol(
    const locationt &location,
    const symbolt &template_symbol,
    const cpp_template_args_tct &specialization_template_args,
    const cpp_template_args_tct &full_template_args);  

  void elaborate_class_template(
    const typet &type);

  const symbolt &instantiate_template(
    const locationt &location,
    const symbolt &symbol,
    const cpp_template_args_tct &specialization_template_args,
    const cpp_template_args_tct &full_template_args,
    const typet &specialization=typet(ID_nil));

  void elaborate_class_template(
    const locationt &location,
    const symbol_typet &type);

  unsigned template_counter;
  unsigned anon_counter;

  template_mapt template_map;

  std::string template_suffix(
    const cpp_template_args_tct &template_args);

  void convert_arguments(
    const irep_idt &mode,
    code_typet &function_type);

  void convert_argument(
    const irep_idt &mode,
    code_typet::argumentt &argument);

  //
  // Misc
  //

  void find_constructor(
    const typet &dest_type,
    exprt &symbol_expr);

  void default_ctor(
    const locationt& location,
    const irep_idt &base_name,
    cpp_declarationt& ctor) const;

  void default_cpctor(
    const symbolt&, cpp_declarationt& cpctor) const;

  void default_assignop(
      const symbolt& symbol, cpp_declarationt& cpctor);

  void default_assignop_value(
      const symbolt& symbol, cpp_declaratort& declarator);

  void default_dtor(const symbolt& symb, cpp_declarationt& dtor);

  codet dtor(const symbolt &symb);

  void check_member_initializers(
    const irept &bases,
    const struct_typet::componentst &components,
    const irept &initializers);

  bool check_component_access(
    const struct_union_typet::componentt &component,
    const struct_union_typet &struct_union_type);

  void full_member_initialization(
    const struct_typet &struct_type,
    irept &initializers);

  bool find_cpctor(const symbolt& symbol)const;
  bool find_assignop(const symbolt& symbol)const;
  bool find_dtor(const symbolt& symbol)const;

  bool find_parent(
    const symbolt& symb,
    const irep_idt &base_name,
    irep_idt &identifier);

  bool get_component(
      const locationt& location,
      const exprt& object,
      const irep_idt& component_name,
      exprt& member);

  void new_temporary(const locationt &location,
                     const typet &,
                     const exprt::operandst &ops,
                     exprt &temporary);

  void new_temporary(const locationt &location,
                     const typet &,
                     const exprt &op,
                     exprt &temporary);

  void static_and_dynamic_initialization();
  void do_not_typechecked();
  void clean_up();

  void add_base_components(
        const struct_typet &from,
        const irep_idt& access,
        struct_typet &to,
        std::set<irep_idt>& bases,
        std::set<irep_idt>& vbases,
        bool is_virtual);

  bool cast_away_constness(const typet &t1,
                           const typet &t2) const;

  void do_virtual_table(const symbolt& symbol);

  // we need to be able to delay the typechecking
  // of function bodies to handle methods with
  // bodies in the class definition
  struct function_bodyt
  {
  public:
    function_bodyt(
      symbolt *_function_symbol,
      const template_mapt &_template_map,
      const instantiation_stackt &_instantiation_stack):
      function_symbol(_function_symbol),
      template_map(_template_map),
      instantiation_stack(_instantiation_stack)
    {
    }
    
    symbolt *function_symbol;
    template_mapt template_map;
    instantiation_stackt instantiation_stack;
  };
  
  typedef std::list<function_bodyt> function_bodiest;
  function_bodiest function_bodies;
  
  void add_function_body(symbolt *_function_symbol)
  {
    function_bodies.push_back(function_bodyt(
      _function_symbol, template_map, instantiation_stack));
  }

  // types

  bool convert_typedef(typet &type);
  void typecheck_type(typet &type);

  cpp_scopet &typecheck_template_parameters(
    template_typet &type);

  void typecheck_compound_type(struct_union_typet &type);
  void check_fixed_size_array(typet &type);
  void typecheck_enum_type(typet &type);

  // determine the scope into which a tag goes
  // (enums, structs, union, classes)
  cpp_scopet &tag_scope(
    const irep_idt &_base_name,
    bool has_body,
    bool tag_only_declaration);

  void typecheck_compound_declarator(
    const symbolt &symbol,
    const cpp_declarationt &declaration,
    cpp_declaratort &declarator,
    struct_typet::componentst &components,
    const irep_idt &access,
    bool is_static,
    bool is_typedef,
    bool is_mutable);

  void typecheck_friend_declaration(
    symbolt &symbol,
    cpp_declarationt &cpp_declaration);

  void put_compound_into_scope(const struct_union_typet::componentt &component);
  void typecheck_compound_body(symbolt &symbol);
  void typecheck_enum_body(symbolt &symbol);
  void typecheck_function_bodies();
  void typecheck_compound_bases(struct_typet &type);
  void add_anonymous_members_to_scope(const symbolt &struct_union_symbol);

  void move_member_initializers(
    irept &initializers,
    const typet &type,
    exprt &value);

  void typecheck_member_function(
    const irep_idt &compound_symbol,
    struct_typet::componentt  &component,
    irept &initializers,
    typet &method_qualifier,
    exprt &value);

  void adjust_method_type(
    const irep_idt &compound_symbol,
    typet &method_type,
    typet &type);

  // for function overloading
  irep_idt function_identifier(const typet &type);

  void zero_initializer(
    const exprt &object,
    const typet &type,
    const locationt &location,
    exprt::operandst &ops);

  // code conversion
  virtual void typecheck_code(codet &code);
  virtual void typecheck_catch(codet &code);
  virtual void typecheck_member_initializer(codet &code);
  virtual void typecheck_decl(codet &code);
  virtual void typecheck_block(codet &code);
  virtual void typecheck_ifthenelse(code_ifthenelset &code);
  virtual void typecheck_while(code_whilet &code);
  virtual void typecheck_switch(code_switcht &code);

  const struct_typet &this_struct_type();

  codet cpp_destructor(
      const locationt &location,
      const typet &type,
      const exprt &object);

  // expressions
  void explicit_typecast_ambiguity(exprt &expr);
  void typecheck_expr_main(exprt &expr);
  void typecheck_expr_member(exprt &expr);
  void typecheck_expr_ptrmember(exprt &expr);
  void typecheck_expr_throw(exprt &expr);
  void typecheck_function_expr(exprt &expr,
                      const cpp_typecheck_fargst &fargs);
  void typecheck_expr_cpp_name(exprt &expr,
                      const cpp_typecheck_fargst &fargs);
  void typecheck_expr_member(exprt &expr,
                      const cpp_typecheck_fargst &fargs);
  void typecheck_expr_ptrmember(exprt &expr,
                      const cpp_typecheck_fargst &fargs);
  void typecheck_cast_expr(exprt &expr);
  void typecheck_expr_trinary(if_exprt &expr);
  void typecheck_expr_binary_arithmetic(exprt &expr);
  void typecheck_expr_explicit_typecast(exprt &expr);
  void typecheck_expr_explicit_constructor_call(exprt &expr);
  void typecheck_expr_address_of(exprt &expr);
  void typecheck_expr_dereference(exprt &expr);
  void typecheck_expr_function_identifier(exprt &expr);
  void typecheck_expr_reference_to(exprt &expr);
  void typecheck_expr_this(exprt &expr);
  void typecheck_expr_new(exprt &expr);
  void typecheck_expr_sizeof(exprt &expr);
  void typecheck_expr_delete(exprt &expr);
  void typecheck_expr_side_effect(side_effect_exprt &expr);
  void typecheck_side_effect_assignment(exprt &expr);
  void typecheck_side_effect_inc_dec(side_effect_exprt &expr);
  void typecheck_expr_typecast(exprt &expr);
  void typecheck_expr_index(exprt& expr);
  void typecheck_expr_rel(exprt& expr);
  void typecheck_expr_comma(exprt &expr);

  void typecheck_function_call_arguments(
    side_effect_expr_function_callt &expr);

  bool operator_is_overloaded(exprt &expr);
  bool overloadable(const exprt &expr);

  void add_implicit_dereference(exprt &expr);

  void typecheck_side_effect_function_call(
                     side_effect_expr_function_callt &expr);

  void typecheck_method_application(
                    side_effect_expr_function_callt &expr);

  void typecheck_assign(codet &code);

public:
  //
  // Type Conversions
  //

  bool standard_conversion_lvalue_to_rvalue(
    const exprt &expr, exprt &new_expr) const;

  bool standard_conversion_array_to_pointer(
    const exprt &expr, exprt &new_expr) const;

  bool standard_conversion_function_to_pointer(
    const exprt &expr, exprt &new_expr) const;

  bool standard_conversion_qualification(
    const exprt &expr, const typet&, exprt &new_expr) const;

  bool standard_conversion_integral_promotion(
    const exprt &expr, exprt &new_expr) const;

  bool standard_conversion_floating_point_promotion(
    const exprt &expr, exprt &new_expr) const;

  bool standard_conversion_integral_conversion(
    const exprt &expr, const typet &type, exprt &new_expr) const;

  bool standard_conversion_floating_integral_conversion(
    const exprt &expr, const typet &type, exprt &new_expr) const;

  bool standard_conversion_floating_point_conversion(
    const exprt &expr, const typet &type, exprt &new_expr) const;

  bool standard_conversion_pointer(
    const exprt &expr, const typet &type, exprt &new_expr);

  bool standard_conversion_pointer_to_member(
    const exprt &expr, const typet &type, exprt &new_expr);

  bool standard_conversion_boolean(
    const exprt &expr, exprt &new_expr) const;

  bool standard_conversion_sequence(
    const exprt &expr, const typet &type, exprt &new_expr, unsigned &rank);

  bool user_defined_conversion_sequence(
    const exprt &expr, const typet &type, exprt &new_expr, unsigned &rank);

  bool reference_related(
    const exprt &expr, const typet &type) const;

  bool reference_compatible(
    const exprt &expr, const typet &type, unsigned &rank) const;

  bool reference_binding(
    exprt expr, const typet &type, exprt &new_expr, unsigned &rank);

  bool implicit_conversion_sequence(
    const exprt &expr, const typet &type, exprt &new_expr, unsigned &rank);

  bool implicit_conversion_sequence(
    const exprt &expr, const typet &type, unsigned &rank);

  bool implicit_conversion_sequence(
    const exprt &expr, const typet &type, exprt &new_expr);

  void reference_initializer(exprt &expr, const typet &type);

  virtual void implicit_typecast(exprt &expr, const typet &type);

  void get_bases(const struct_typet &type,
     std::set<irep_idt> &set_bases) const;

  void get_virtual_bases(const struct_typet &type,
     std::list<irep_idt> &vbases) const;

  bool subtype_typecast(
    const struct_typet &from,
    const struct_typet &to) const;

  void make_ptr_typecast(
    exprt &expr,
    const typet & dest_type);

  // the C++ typecasts

  bool const_typecast(
    const exprt &expr,
    const typet &type,
    exprt &new_expr);

  bool dynamic_typecast(
    const exprt &expr,
    const typet &type,
    exprt &new_expr);

  bool reinterpret_typecast(
    const exprt &expr,
    const typet &type,
    exprt &new_expr,
    bool check_constantness=true);

  bool static_typecast(
    const exprt &expr,
    const typet &type,
    exprt &new_expr,
    bool check_constantness=true);

private:
  typedef std::list<irep_idt> dynamic_initializationst;
  dynamic_initializationst dynamic_initializations;
  bool disable_access_control;           // Disable protect and private
};

#endif
