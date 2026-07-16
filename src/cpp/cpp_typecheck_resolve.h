/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_TYPECHECK_RESOLVE_H
#define CPROVER_CPP_CPP_TYPECHECK_RESOLVE_H

#include "cpp_template_args.h"
#include "cpp_scopes.h"

class cpp_namet;
class cpp_typecheck_fargst;
class cpp_declarationt;
class symbol_table_baset;

// N5008 [temp.constr.order]/1 + [temp.func.order]: true iff declaration p is
// STRICTLY more constrained than q (p's associated constraints subsume q's
// but not vice versa).  Used by overload resolution and by the
// class-template partial-specialization search
// ([temp.class.spec.match]/2).
bool template_constraint_strictly_subsumes(
  const symbol_table_baset &symbol_table,
  const cpp_declarationt &p,
  const cpp_declarationt &q);

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

  /// Clear the static resolve_scope cache. Must be called between
  /// type-checking different translation units.

  void guess_template_args(
    const typet &template_parameter,
    const typet &desired_type);

  void guess_template_args(
    const exprt &template_parameter,
    const exprt &desired_expr);

  /// Deduce a function parameter pack ([temp.deduct.type]/9-10): match the
  /// pack pattern against each remaining desired parameter and record the
  /// element types in the template map for later expansion.
  /// \param pack_decl: pre-conversion cpp_declaration of the pack parameter
  /// \param desired_code_type: the desired (argument) code type
  /// \param start_index: index of the first desired parameter the pack covers
  void deduce_function_parameter_pack(
    const cpp_declarationt &pack_decl,
    const typet &desired_code_type,
    std::size_t start_index);

protected:
  cpp_typecheckt &cpp_typecheck;
  source_locationt source_location;
  cpp_scopet *original_scope;

  /// Pack parameters whose elements were deduced via the derived-to-base
  /// rule ([temp.deduct.call]/4.3): the function parameter is a class
  /// template-id `C<..., P...>` and the call argument is of a class type
  /// *derived* from a specialization of `C`, so the pack `P` is deduced from
  /// the base-class subobject.  In that case build_template_args emits a
  /// single placeholder for `P` and the deduced elements must be expanded to
  /// the full arity (see the expansion in guess_function_template_args);
  /// directly-deduced packs (where the argument is the template itself, not a
  /// derived class) are already handled by the existing machinery and must
  /// not be re-expanded here.  Keyed by the pack parameter's identifier.
  std::set<irep_idt> derived_to_base_deduced_packs;

  /// True while re-deducing against a base-class subobject inside the
  /// derived-to-base branch of guess_template_args, so the pack-matching code
  /// records the deduced pack(s) in \ref derived_to_base_deduced_packs.
  bool deducing_against_base = false;

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

  /// N5008 [over.match.funcs]/5: cv penalty (0 or 1) for selecting a const
  /// member function *template* candidate when called on a non-const object,
  /// recovered from the candidate template's ID_method_qualifier (the deduced
  /// function type of an uninstantiated template_function_instance carries no
  /// `this` parameter, so disambiguate_functions cannot rank it).
  unsigned member_template_const_penalty(
    const exprt &cand,
    const cpp_typecheck_fargst &fargs);

  void filter(
    resolve_identifierst &identifiers,
    const wantt want);

  typet disambiguate_template_classes(
    const irep_idt &base_name,
    const cpp_scopest::id_sett &id_set,
    const cpp_template_args_non_tct &template_args,
    bool qualified = false);

  typet resolve_template_alias(
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

  bool disambiguate_functions(
    const exprt &expr,
    unsigned &args_distance,
    const cpp_typecheck_fargst &fargs,
    unsigned *cv_distance = nullptr);

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
    std::size_t constrained_args;
    std::size_t repeated_params;
    cpp_template_args_tct specialization_args;
    cpp_template_args_tct full_args;
    irep_idt id;
    // The specialization arguments used to actually instantiate the selected
    // template.  Normally identical to `specialization_args`, but for a
    // partial specialization ending in a parameter pack this holds the pack
    // expanded into one positional argument per deduced element
    // (N5008 [temp.variadic]/5), whereas `specialization_args` (and hence
    // `cost`) keeps the un-expanded form so that partial-ordering selection is
    // not perturbed by the pack arity.
    cpp_template_args_tct instantiation_args;
    matcht(
      cpp_template_args_tct _s_args,
      cpp_template_args_tct _f_args,
      irep_idt _id,
      std::size_t _constrained = 0,
      std::size_t _repeated = 0)
      : cost(_s_args.arguments().size()),
        constrained_args(_constrained),
        repeated_params(_repeated),
        specialization_args(_s_args),
        full_args(_f_args),
        id(_id),
        instantiation_args(_s_args)
    {
    }

    bool operator<(const matcht &other) const
    {
      if(cost != other.cost)
        return cost < other.cost;
      // Prefer more constrained specializations (more non-trivial
      // patterns in the partial specialization arguments).
      if(constrained_args != other.constrained_args)
        return constrained_args > other.constrained_args;
      // Prefer specializations with repeated parameters (equality
      // constraints like <T, T>) over concrete arguments (<T, int>).
      return repeated_params > other.repeated_params;
    }
  };
};

#endif // CPROVER_CPP_CPP_TYPECHECK_RESOLVE_H
