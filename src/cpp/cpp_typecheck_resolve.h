/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_TYPECHECK_RESOLVE_H
#define CPROVER_CPP_CPP_TYPECHECK_RESOLVE_H

#include "cpp_typecheck_fargs.h"
#include "cpp_name.h"
#include "cpp_template_args.h"
#include "cpp_scopes.h"

class cpp_typecheck_resolvet
{
public:
  cpp_typecheck_resolvet(
    class cpp_typecheckt &_cpp_typecheck);

  enum class wantt { VAR, TYPE, BOTH };

  exprt resolve(
    const cpp_namet &cpp_name,
    const wantt want,
    const cpp_typecheck_fargst &fargs,
    bool fail_with_exception=true);

  // Returns the scope as a side-effect as 'current_scope'.
  // Should really return explicitly.
  cpp_scopet &resolve_scope(
    const cpp_namet &cpp_name,
    irep_idt &base_name,
    cpp_template_args_non_tct &template_args);

  cpp_scopet &resolve_namespace(const cpp_namet &cpp_name);

protected:
  cpp_typecheckt &cpp_typecheck;
  source_locationt source_location;
  cpp_scopet *original_scope;

  typedef std::vector<exprt> resolve_identifierst;

  void convert_identifiers(
    const cpp_scopest::id_sett &id_set,
    const cpp_typecheck_fargst &fargs,
    resolve_identifierst &identifiers);

  exprt convert_template_parameter(
    const cpp_idt &id);

  exprt convert_identifier(
    const cpp_idt &id,
    const cpp_typecheck_fargst &fargs);

  void disambiguate_functions(
    resolve_identifierst &identifiers,
    const cpp_typecheck_fargst &fargs);

  void exact_match_functions(
    resolve_identifierst &identifiers,
    const cpp_typecheck_fargst &fargs);

  void filter(
    resolve_identifierst &identifiers,
    const wantt want);

  struct_tag_typet disambiguate_template_classes(
    const irep_idt &base_name,
    const cpp_scopest::id_sett &id_set,
    const cpp_template_args_non_tct &template_args);

  void make_constructors(
    resolve_identifierst &identifiers);

  void apply_template_args(
    resolve_identifierst &identifiers,
    const cpp_template_args_non_tct &template_args,
    const cpp_typecheck_fargst &fargs);

  void apply_template_args(
    exprt &expr,
    const cpp_template_args_non_tct &template_args,
    const cpp_typecheck_fargst &fargs);

  void guess_function_template_args(
    resolve_identifierst &identifiers,
    const cpp_typecheck_fargst &fargs);

  void remove_templates(
    resolve_identifierst &identifiers);

  void remove_duplicates(
    resolve_identifierst &identifiers);

  exprt guess_function_template_args(
    const exprt &expr,
    const cpp_typecheck_fargst &fargs);

  void guess_template_args(
    const typet &template_parameter,
    const typet &desired_type);

  void guess_template_args(
    const exprt &template_parameter,
    const exprt &desired_expr);

  bool disambiguate_functions(
    const exprt &expr,
    unsigned &args_distance,
    const cpp_typecheck_fargst &fargs);

  void resolve_argument(
    exprt &argument,
    const cpp_typecheck_fargst &fargs);

  exprt do_builtin(
    const irep_idt &base_name,
    const cpp_typecheck_fargst &fargs,
    const cpp_template_args_non_tct &template_args);

  void show_identifiers(
    const irep_idt &base_name,
    const resolve_identifierst &identifiers,
    std::ostream &out);

  void resolve_with_arguments(
    cpp_scopest::id_sett &id_set,
    const irep_idt &base_name,
    const cpp_typecheck_fargst &fargs);

  void filter_for_named_scopes(cpp_scopest::id_sett &id_set);
  void filter_for_namespaces(cpp_scopest::id_sett &id_set);

  struct matcht
  {
    std::size_t cost;
    cpp_template_args_tct specialization_args;
    cpp_template_args_tct full_args;
    irep_idt id;
    matcht(
      cpp_template_args_tct _s_args,
      cpp_template_args_tct _f_args,
      irep_idt _id):
      cost(_s_args.arguments().size()),
      specialization_args(_s_args),
      full_args(_f_args),
      id(_id)
    {
    }

    bool operator<(const matcht &other) const
    {
      return cost<other.cost;
    }
  };
};

#endif // CPROVER_CPP_CPP_TYPECHECK_RESOLVE_H
