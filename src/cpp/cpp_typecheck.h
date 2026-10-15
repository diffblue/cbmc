/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_TYPECHECK_H
#define CPROVER_CPP_CPP_TYPECHECK_H

#include <util/std_code_base.h>

#include <ansi-c/c_typecheck_base.h>

#include "cpp_parse_tree.h"
#include "cpp_scopes.h"
#include "cpp_target_type.h"
#include "cpp_typecheck_resolve.h"
#include "template_map.h"

#include <limits>
#include <list>
#include <set>
#include <unordered_set>
#include <vector>

class pointer_typet;
class reference_typet;

bool cpp_typecheck(
  cpp_parse_treet &cpp_parse_tree,
  symbol_table_baset &symbol_table,
  const std::string &module,
  message_handlert &message_handler);

bool cpp_typecheck(
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns);

/// Thrown by `typecheck_template_args` when an explicit template argument has
/// the wrong *kind* (a non-type argument supplied for a type parameter, or
/// vice versa) while matching a candidate during overload resolution.  Per
/// N5008 [temp.arg]/2 and [temp.deduct]/8 this is a deduction failure that
/// removes only that candidate from the overload set, so the candidate loop in
/// `apply_template_args` catches it and skips the candidate rather than
/// treating it as a hard error.
void expand_member_initializer_packs_in_body(
  irept &node,
  const template_mapt::pack_args_mapt &pack_args_map,
  const template_mapt::pack_expr_mapt &pack_expr_map);

class template_arg_kind_mismatch_exceptiont
{
};

/// Thrown when type-checking fails because a class that is only DECLARED so
/// far is required to be complete (N5008 [expr.sizeof]/1, [class.mem]).  A
/// class template specialization being instantiated when this happens
/// cannot be completed YET; typecheck_compound_type puts the incomplete
/// instance back so that a later context requiring the complete type (after
/// the class is defined, [temp.point]) instantiates it again.
class incomplete_dependency_exceptiont
{
};

/// The C++ type bool for the front end's internal ID_bool (the type of a
/// comparison or logical expression); any other type unchanged.
typet cpp_bool_type(const typet &type);

class cpp_typecheckt:public c_typecheck_baset
{
public:
  cpp_typecheckt(
    cpp_parse_treet &_cpp_parse_tree,
    symbol_table_baset &_symbol_table,
    const std::string &_module,
    message_handlert &message_handler);

  cpp_typecheckt(
    cpp_parse_treet &_cpp_parse_tree,
    symbol_table_baset &_symbol_table1,
    const symbol_table_baset &_symbol_table2,
    const std::string &_module,
    message_handlert &message_handler);

  /// N5008 [temp.inst]/2: implicitly instantiate the class template
  /// specialization \p type names, in a context where the completeness of
  /// the class affects the semantics (overload viability of a conversion
  /// to it, for instance).  Does nothing for other types.
  void require_complete_type(const typet &type)
  {
    elaborate_class_template(type);
  }

  ~cpp_typecheckt() override
  {
  }

  void typecheck() override;

  // overload to use C++ syntax
  std::string to_string(const typet &) override;
  std::string to_string(const exprt &) override;

  /// In C++ the empty braced-init-list `{}` value-initializes a scalar
  /// per [dcl.init.list]/3.10.  Strictly this is a C++11 feature, but
  /// CBMC's earlier `--cppNN` modes already accept many C++11
  /// constructs as permissive extensions, so we always return true.
  bool empty_brace_value_initializes_scalar() const override;

  /// N5008 [dcl.init.aggr]/5.1: the value of a member's default member
  /// initializer, type-checked in the scope of its class, for an aggregate
  /// element the initializer list left out.
  std::optional<exprt> default_member_initializer_value(
    const struct_tag_typet &struct_tag_type,
    const struct_union_typet::componentt &component,
    const source_locationt &source_location,
    bool force_constant) override;

  /// N5008 [class]/4 + [expr.sizeof]/2: sizeof a class type is never 0.
  bool sizeof_yields_nonzero_for_class() const override
  {
    return true;
  }

  friend class cpp_typecheck_resolvet;
  friend class cpp_declarator_convertert;
  friend class cpp_typecheck_fargst;

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

  void typecheck_expr(exprt &) override;

  /// Variant of \ref typecheck_expr that propagates an optional target
  /// type for use by deduction and conversion paths
  /// ([temp.deduct.funcaddr]/1, [temp.deduct.conv]/1,
  /// [over.ics.list], [dcl.init.list]).  See `cpp_target_type.h`.
  ///
  /// Phase 1 of the target-type-threading refactor: the parameter is
  /// accepted but unused — every callee sees the existing isolated
  /// typecheck.  Subsequent phases consume the target in the relevant
  /// per-kind handlers.  See
  /// `doc/architectural/cpp-frontend-plan-target-type-threading.md`.
  void typecheck_expr(exprt &expr, const target_typet &target);

  bool cpp_is_pod(const typet &type) const;

  /// Convert the parameters of \p code_type that are still in parsed form
  /// (cpp_declaration) to `parameter's; leave the type unchanged if one of
  /// them is a pack expansion or dependent.
  void convert_parsed_parameters(code_typet &code_type);

  void pin_constructor_parameter_class_names(cpp_declaratort &declarator);

  /// Instantiate the out-of-class definition \p member_type of the member
  /// class \p member_name for the existing specializations of the class
  /// template \p outer_template ([temp.mem.class]/1, [temp.inst]/3).
  void complete_member_class_of_instances(
    const cpp_idt &outer_template,
    const irep_idt &member_name,
    const typet &member_type);

  /// Which one-argument constructors of \p class_type accept \p value by a
  /// standard conversion or reference binding: no explicit one, only
  /// explicit ones (then copy-initialization from \p value is ill-formed,
  /// [over.match.copy]/1.1, [class.conv.ctor]/2), or explicit and converting
  /// ones.
  enum class explicit_constructorst
  {
    NONE_VIABLE,
    ONLY_EXPLICIT,
    ALSO_CONVERTING
  };
  explicit_constructorst viable_one_argument_constructors(
    const struct_tag_typet &class_type,
    const exprt &value);

  /// Whether the braced-init-list \p list can aggregate-initialize an
  /// object of the aggregate type \p type (an array, or a class the front
  /// end treats as POD), with brace elision ([dcl.init.aggr]/16).
  /// N5008 [over.ics.list]/8: such a list argument converts to an
  /// aggregate parameter by a user-defined conversion sequence.
  bool
  aggregate_list_initialization_is_viable(const exprt &list, const typet &type);

  /// True if default-constructing an object of \p type must run at least one
  /// default member initializer (NSDMI), directly or in a subobject (a member
  /// of class type, or an element of an array of class type).  Per N5008
  /// [class.default.ctor]/3 such a class has a non-trivial default
  /// constructor, so a value-less object must be default-constructed rather
  /// than merely zero-initialized.  This is intentionally separate from
  /// cpp_is_pod, which continues to report such a class as a POD because it
  /// governs braced *aggregate* initialization -- permitted for aggregates
  /// with NSDMIs since C++14 ([dcl.init.aggr]).
  bool has_default_member_initializer(const typet &type) const;
  /// Whether the (innermost) element type of \p array_type is a class with
  /// a user-provided constructor other than a default or copy/move one, so
  /// that each element is constructed from its own initializer-clause
  /// rather than aggregate-initialized ([dcl.init.aggr]/1,
  /// [dcl.init.list]/3).
  bool array_elements_have_user_constructor(const typet &array_type);

  /// The arguments of a parenthesized initializer `T x(args)'.  N5008
  /// [dcl.init.general]/16.6.2: `T x({})' passes ONE argument, the empty
  /// braced-init-list, to a constructor of T; it is not the value-
  /// initialization `T x{}' ([dcl.init.list]/3.5).  The empty list is marked
  /// (ID_C_paren_init) so that cpp_constructor does not take it as the
  /// latter: `function_cfg_infot cfg_info({})' found no constructor of a
  /// class without a default constructor (CBMC's own contracts.cpp,
  /// dog-fooding).
  static exprt::operandst
  paren_init_arguments(const exprt::operandst &arguments);

  std::optional<codet> cpp_constructor(
    const source_locationt &source_location,
    const exprt &object,
    const exprt::operandst &operands);

protected:
  cpp_scopest cpp_scopes;

  /// N5008 [class.access]/[class.access.base]: accessibility is judged
  /// from the point of use.  During overload resolution the current
  /// scope is moved into candidate classes (e.g. while binding
  /// constructor arguments), so accessibility checks that only walk the
  /// current scope chain lose the caller's context -- in particular the
  /// derived-to-base conversion check in `base_publicly_accessible`,
  /// which must honour FRIENDSHIP of the point of use
  /// ([class.access.base]/4).  `resolve_scope` records the scope the
  /// name was written in here; RAII-restored by the resolver.
  cpp_scopet *access_judgment_scope = nullptr;

  /// While the body of an IMPLICITLY-DEFINED constructor or destructor is
  /// being converted, the class it belongs to.  N5008
  /// [class.access.general]/4 + [class.default.ctor]/4: such a definition
  /// is a member of its class, so the member initializations it performs
  /// may name the class's OWN private members -- but not a base's
  /// (regression/cpp/Protection1).  Hence an exact-match context rather
  /// than a scope chain.
  irep_idt implicit_definition_class;
  // SFINAE alternative declarations: when two function templates differ
  // only in their SFINAE constraints, the second is stored here (keyed
  // by the primary's symbol name) rather than in the symbol table, to
  // avoid triggering extra instantiations during symbol table iteration.
  std::map<irep_idt, symbolt> sfinae_alternatives;

  // N5008 [temp.inst]/1, [temp.point]: a class template specialization is
  // implicitly instantiated -- and thereby completed -- only from a
  // *definition* of the template.  This set records the symbol names of class
  // templates (primary templates and partial specializations) for which a
  // definition (a class body) has been seen; typecheck_class_template inserts
  // into it and elaborate_class_template consults it to refuse instantiating a
  // specialization of a template that has so far only been forward-declared
  // (which would fabricate a spurious empty class and permanently mask the
  // members a later definition adds).  It is kept here rather than as a marker
  // on the declaration irep so that recording a definition never perturbs
  // template argument matching or specialization ordering, which compare and
  // hash the declaration.
  std::set<irep_idt> defined_class_templates;

  /// Nesting depth of active `sfinae_contextt` guards (substitution / deduction
  /// / overload resolution, N5008 [temp.deduct]/8).  Non-zero means a
  /// substitution failure is a SFINAE failure that must stay silent; zero means
  /// an ordinary context where an unresolved call is a genuine, diagnosable
  /// error.  Maintained by `sfinae_contextt` (a friend).
  unsigned sfinae_context_depth = 0;

  // Nonzero while a partial-specialization argument PATTERN is being
  // matched/typechecked ([temp.spec.partial.match]); gates the
  // two-phase-lookup declaration-order filter in resolve() (N5008
  // [temp.res.general]/1, [temp.dep.candidate]/1).
  unsigned two_phase_pattern_depth = 0;

  // Non-zero while operator_is_overloaded gathers/resolves candidates for
  // an operator EXPRESSION (a @ b).  N5008 [over.match.oper]/3: only there
  // does the non-member candidate lookup ignore member functions and add
  // ADL candidates regardless of an in-scope member.  An EXPLICIT call
  // `operator@(x)` uses ordinary [over.call.func] rules instead: a member
  // found by unqualified lookup makes it a member call and suppresses ADL
  // ([basic.lookup.argdep]/1).
  unsigned operator_expr_lookup_depth = 0;

  /// Records a pending "no viable function" failure: set by resolve() when, in
  /// an ordinary (non-SFINAE) context, a call's only candidates are function
  /// templates all removed by [temp.deduct]/8 substitution failures.  The
  /// silent `throw 0` is kept (so recoverable callers can still absorb it via
  /// `catch(int)`), but this flag lets typecheck_method_bodies distinguish an
  /// UNRECOVERED such failure -- which must be diagnosed and NOT rolled back as
  /// unsupported-STL leniency -- from an ordinary suppressible instantiation
  /// failure.  It is cleared at every resolve() entry, so it only survives when
  /// the throw propagates straight to the body's conversion without any
  /// intervening (recovering) resolution.
  bool pending_no_viable_call = false;

  /// Non-zero while overload resolution is exploring a class's
  /// CONSTRUCTOR candidates as part of a user-defined conversion
  /// sequence (copy-initialization, [over.match.copy]).  N5008
  /// [over.best.ics]/4: when the target is the first parameter of such a
  /// constructor candidate, user-defined conversion sequences are NOT
  /// considered -- otherwise a `template <class C> operator C()` on the
  /// argument makes EVERY constructor viable (C deduced as each
  /// parameter type) and resolution reports a bogus ambiguity.
  unsigned copy_init_ctor_exploration = 0;

  /// (destination class, source type, value category, component count) for
  /// which the constructor-template trial of user_defined_conversion_sequence
  /// found no conversion; see there
  std::unordered_set<std::string> failed_template_conversions;

  /// The class templates that have out-of-class member definitions
  /// (ID_template_methods), in the order they received the first one.  The
  /// searches for a member's out-of-class definition consider only these;
  /// scanning the whole symbol table for them on every bodiless member of
  /// every instantiation dominated the type-checking time of large
  /// translation units (goto_instrument_parse_options.cpp).
  std::vector<irep_idt> templates_with_out_of_class_members;

  std::unordered_set<irep_idt> templates_with_out_of_class_members_set;
  /// A (name, symbol) entry of templates_with_out_of_class_member_symbols,
  /// shaped like a symbol-table entry
  struct template_with_members_entryt
  {
    const irep_idt &first;
    const symbolt &second;
  };
  /// The symbols of templates_with_out_of_class_members
  std::vector<template_with_members_entryt>
  templates_with_out_of_class_member_symbols() const;

  /// See template_by_first_parameter
  symbolt *template_by_first_parameter(const std::string &param_id);
  std::unordered_map<std::string, irep_idt> templates_by_first_parameter;
  /// number of rescans (statistics)
  std::size_t templates_by_first_parameter_scanned = 0;
  irep_idt pending_no_viable_base_name;
  source_locationt pending_no_viable_location;

  cpp_parse_treet &cpp_parse_tree;
  irep_idt current_linkage_spec;

  void convert(cpp_linkage_spect &);
  void convert(cpp_namespace_spect &);
  void convert(cpp_usingt &);
  void convert(cpp_itemt &);
  void convert(cpp_declarationt &);
  void convert(cpp_declaratort &);
  void convert(cpp_static_assertt &);
  static void
  propagate_constants(exprt &expr, const symbol_table_baset &symbol_table);

  void convert_initializer(symbolt &symbol);
  bool has_non_pod_class_member(const struct_union_typet &type);
  bool has_user_declared_constructor(const struct_typet &type);
  void aggregate_member_initialization(
    const exprt &object,
    const struct_typet &struct_type,
    const exprt::operandst &ops,
    const source_locationt &source_location,
    code_blockt &block);
  void convert_function(symbolt &symbol);

  typet decltype_of(const exprt &e, bool parenthesized);
  typet deduce_placeholder_type(
    const typet &declared,
    const exprt &initializer,
    bool parenthesized);
  void deduce_return_type(code_frontend_returnt &code);

  /// The declared return type of the function being converted, when it
  /// contains a placeholder ([dcl.type.auto.deduct]/2.1: the T of each
  /// non-discarded return statement); c_typecheck_baset::return_type holds
  /// the running deduction ([dcl.spec.auto.general]/13).
  typet declared_return_type;
  /// The function type of the function being converted, so that a deduced
  /// return type is visible to the rest of the body (a recursive call after
  /// the first return statement, [dcl.spec.auto.general]/13, Example 4).
  code_typet *deducing_function_type = nullptr;

  /// Return-type context for a function body type-checked outside
  /// convert_function (the lambda lowerings): installs the declared return
  /// type of \p function_type (a placeholder when \p deduce is set) for the
  /// body's return statements and restores the enclosing function's context
  /// on every exit -- if the body throws and an upstream recovery absorbs it
  /// while the ENCLOSING body continues, its later return statements must
  /// still convert against its own return type ([stmt.return]/3).  After the
  /// body, finish() applies [dcl.spec.auto.general]/11 (no non-discarded
  /// return statement: void).
  class return_deduction_contextt
  {
  public:
    return_deduction_contextt(
      cpp_typecheckt &_typecheck,
      code_typet &_function_type,
      bool deduce);
    ~return_deduction_contextt();
    void finish();

  private:
    cpp_typecheckt &typecheck;
    code_typet &function_type;
    const typet saved_return_type;
    const typet saved_declared_return_type;
    code_typet *const saved_deducing_function_type;
  };

  void convert_pmop(exprt &expr);

  codet convert_anonymous_union(cpp_declarationt &declaration);

  void convert_anon_struct_union_member(
    const cpp_declarationt &declaration,
    const irep_idt &access,
    struct_typet::componentst &components);

  //
  // Templates
  //
  void salvage_default_arguments(
    const template_typet &old_type,
    template_typet &new_type);

  void convert_template_declaration(cpp_declarationt &declaration);

  void convert_non_template_declaration(cpp_declarationt &declaration);

  void convert_template_function_or_member_specialization(
    cpp_declarationt &declaration);

  void convert_class_template_specialization(
    cpp_declarationt &declaration);

  void typecheck_class_template(cpp_declarationt &declaration);

  void typecheck_function_template(cpp_declarationt &declaration);
  void typecheck_variable_template(cpp_declarationt &declaration);
  void convert_variable_template_specialization(cpp_declarationt &declaration);

  void typecheck_template_alias(cpp_declarationt &declaration);

  void typecheck_class_template_member(cpp_declarationt &declaration);
  void define_member_template_of_class(cpp_declarationt &declaration);

  std::string class_template_identifier(
    const irep_idt &base_name,
    const template_typet &template_type,
    const cpp_template_args_non_tct &partial_specialization_args);

  // N5008 [temp.over.link]/6: are two function-template declarations'
  // signatures equivalent (identical up to template-parameter renaming
  // and parameter names)?
  static bool function_template_signatures_equivalent(
    const cpp_declarationt &forward,
    const cpp_declarationt &candidate);

  std::string function_template_identifier(
    const irep_idt &base_name,
    const template_typet &template_type,
    const typet &function_type);

  /// \param explicit_only: when true, type-check the given (explicit)
  ///   arguments only; do not append the template's default arguments for
  ///   the remaining parameters
  cpp_template_args_tct typecheck_template_args(
    const source_locationt &source_location,
    const symbolt &template_symbol,
    const cpp_template_args_non_tct &template_args,
    bool explicit_only = false);

  // template instantiations
  class instantiationt
  {
  public:
    source_locationt source_location;
    irep_idt identifier;
    cpp_template_args_tct full_template_args;
  };

  typedef std::list<instantiationt> instantiation_stackt;
  instantiation_stackt instantiation_stack;
  bool had_template_instantiation = false;

  void show_instantiation_stack(std::ostream &);

  class instantiation_levelt
  {
  public:
    instantiation_levelt(
      instantiation_stackt &_instantiation_stack,
      bool &_had_template_instantiation)
      : instantiation_stack(_instantiation_stack),
        had_template_instantiation(_had_template_instantiation)
    {
      instantiation_stack.push_back(instantiationt());
      had_template_instantiation = true;
    }

    ~instantiation_levelt()
    {
      instantiation_stack.pop_back();
    }

  private:
    instantiation_stackt &instantiation_stack;
    bool &had_template_instantiation;
  };

  const symbolt &class_template_symbol(
    const source_locationt &source_location,
    const symbolt &template_symbol,
    const cpp_template_args_tct &specialization_template_args,
    const cpp_template_args_tct &full_template_args);

  bool dropped_base_now_complete(const typet &type) const;
  void erase_instance_members(const symbolt &symbol);
  bool register_lazy_member(
    const cpp_declarationt &declaration,
    const cpp_declaratort &declarator,
    struct_typet::componentst &components,
    const irep_idt &access,
    bool is_static,
    bool is_typedef,
    bool is_mutable);
  /// the class template specializations whose elaborate_class_template is
  /// on the call stack (see there)
  std::set<irep_idt> elaborations_in_progress;
  void elaborate_class_template(const typet &type) override;

  const symbolt &instantiate_template(
    const source_locationt &source_location,
    const symbolt &symbol,
    const cpp_template_args_tct &specialization_template_args,
    const cpp_template_args_tct &full_template_args,
    const typet &specialization = uninitialized_typet{});

  /// Queue the already-bodied (inline) deferred member functions of a
  /// realized class-template instance for type-checking.  Used at the
  /// instance-completion site in `typecheck_compound_type` so that
  /// explicitly/extern-instantiated class templates (e.g.
  /// `std::__cxx11::basic_string<char>`), which are completed through the
  /// incomplete-to-complete swap rather than through `instantiate_template`,
  /// still have their inline member bodies instantiated per N5008
  /// [temp.inst]/4 + Note 4 instead of being discarded by `clean_up()`.
  void queue_deferred_methods_of_instance(const irep_idt &class_id);

  /// Instantiate, by signature (parameter arity) rather than base name, the
  /// out-of-line definition body of a class-template instance member.  Used to
  /// repair a member that was attached the wrong overload's body.  See the
  /// definition for the full rationale (N5008 [over.match], [dcl.fct]/3).
  std::optional<exprt> instantiate_matching_member_body(
    const symbolt &member,
    std::vector<irep_idt> &param_names);

  void elaborate_class_template(
    const source_locationt &source_location,
    const struct_tag_typet &type);

  /// Lazy class-body elaboration primitive per N5008 [temp.inst]/3.
  /// Resolves the type of a class-scope member that was registered
  /// without a fully-elaborated type.  Idempotent on already-complete
  /// members.  See
  /// `doc/architectural/cpp-frontend-plan-lazy-elaboration.md`.
  ///
  /// Phase 1 of the lazy-elaboration refactor (this commit) installs
  /// the API; no caller marks a component lazy yet, so the helper is
  /// a fast no-op that returns the existing component pointer when
  /// found.
  ///
  /// \param struct_type the class whose member is being completed.
  ///        Must be mutable because completion updates the component
  ///        in place.
  /// \param base_name the unqualified name of the member to complete.
  /// \return pointer to the (now-complete) component, or nullptr if
  ///         no component with that base_name exists, or if a lazy
  ///         component's source genuinely fails to resolve.
  struct_union_typet::componentt *ensure_member_complete(
    struct_union_typet &struct_type,
    const irep_idt &base_name);

  /// Const overload of \ref ensure_member_complete.  Used at read-only
  /// component iteration sites (e.g. the resolver's constructor-
  /// candidate filter).  When called on a struct that contains a lazy
  /// component, this overload **cannot** complete it (which would
  /// require mutating the type) and returns nullptr in that case so
  /// the caller can skip rather than read an unresolved type.  When
  /// no lazy markers exist (always true in Phase 1) this is a fast
  /// linear lookup that returns the existing pointer.
  const struct_union_typet::componentt *ensure_member_complete(
    const struct_union_typet &struct_type,
    const irep_idt &base_name);

  /// Bulk-complete every lazy member of a struct in one pass.  Useful
  /// at sites that iterate `struct_type.components()` and read each
  /// component's type — a single pre-iteration call is O(n) instead
  /// of the O(n²) cost of one `ensure_member_complete` per
  /// component.  No-op in Phase 1 (no lazy producer); the helper
  /// exists so Phase 2's caller audit can switch to it without
  /// further refactoring at the call sites.
  void complete_all_components(struct_union_typet &struct_type);

  /// Phase 4 on-demand resolution per N5008 [temp.inst]/3.1: attempt
  /// to resolve a lazy component's placeholder type by re-running
  /// `typecheck_type` in the class scope recorded under
  /// `ID_lazy_type_source`.  The retry is wrapped in
  /// `sfinae_contextt` ([temp.deduct]/8) so substitution failure
  /// does not produce user-visible diagnostics or pollute the error
  /// counter.  Returns true if the component is (or becomes)
  /// resolved; false if it could not be resolved.  Idempotent:
  /// already-resolved components return true immediately.
  bool try_resolve_lazy_member(struct_union_typet::componentt &component);

  /// Sibling of \ref try_resolve_lazy_member for class-scope typedef
  /// *symbols* registered by the producer in `typecheck_compound_body`.
  /// The mechanic is the same: switch into the class scope recorded
  /// under `ID_lazy_type_source`, retry `typecheck_type` under
  /// `sfinae_contextt`, and on success replace the symbol's type
  /// with the resolved one.  Used by the resolver and any other
  /// caller that reads `symbol.type` for a possibly-lazy typedef.
  bool try_resolve_lazy_typedef_symbol(symbolt &sym);

  /// Type-only sibling of the symbol/component helpers.  Operates
  /// directly on a `typet` carrying `ID_C_lazy_member_type`.  Useful
  /// at sites that have a copy of the type but not a back-pointer
  /// to the originating symbol or component (e.g. after the
  /// resolver hands back a typedef expansion).
  bool try_resolve_lazy_type(typet &type);

  unsigned template_counter;
  unsigned anon_counter;

  template_mapt template_map;

  std::string template_suffix(
    const cpp_template_args_tct &template_args);

  cpp_scopet &sub_scope_for_instantiation(
    cpp_scopet &template_scope,
    const std::string &suffix);

  void
  convert_parameters(const irep_idt &current_mode, code_typet &function_type);

  void convert_parameter(
    const irep_idt &current_mode,
    code_typet::parametert &parameter);

  //
  // Misc
  //

  void default_ctor(
    const source_locationt &source_location,
    const irep_idt &base_name,
    cpp_declarationt &ctor) const;

  void default_cpctor(
    const symbolt &,
    cpp_declarationt &cpctor,
    const irep_idt &param_identifier = "ref",
    bool is_move = false) const;

  void default_assignop(
      const symbolt &symbol, cpp_declarationt &cpctor);

  void default_assignop_value(
    const symbolt &symbol,
    cpp_declaratort &declarator,
    bool is_move = false);

  void default_dtor(const symbolt &symb, cpp_declarationt &dtor);

  /// The implicit code of the destructor of \p symb: the base and member
  /// destructor calls (returned, to follow the body) and, in \p prologue,
  /// the installation of the class's virtual pointers (to precede it).
  codet
  dtor(const symbolt &symb, const symbol_exprt &this_expr, codet &prologue);

  void check_member_initializers(
    const struct_typet::basest &bases,
    const struct_typet::componentst &components,
    const irept &initializers,
    const irep_idt &class_identifier = irep_idt(),
    bool is_template_instance = false);

  bool check_component_access(
    const struct_union_typet::componentt &component,
    const struct_union_typet &struct_union_type);

  /// Check that the default constructor selected to default-initialize an
  /// object of class type is accessible at the point of use ([dcl.init],
  /// [expr.new], [class.base.init]/12, [class.access.base]).  Used for
  /// non-static data members (mem-initializer context), local and global
  /// variables, and new-expressions.  \p object_type is the constructed
  /// object's declared type; arrays are checked element-wise.  \p
  /// naming_scope is the point of use, from which accessibility is judged.
  /// Throws a diagnostic if the selected default constructor is
  /// inaccessible.
  void check_default_constructor_access(
    const typet &object_type,
    const source_locationt &source_location,
    cpp_scopet *naming_scope);

  void full_member_initialization(
    const struct_union_typet &struct_union_type,
    irept &initializers);

  bool find_cpctor(const symbolt &symbol)const;
  bool find_assignop(const symbolt &symbol)const;
  bool implicit_copy_assignment_is_deleted(const struct_typet &type);
  bool find_mvctor(const symbolt &symbol) const;
  static void make_move_parameter(cpp_declaratort &declarator);
  bool find_dtor(const symbolt &symbol)const;

  bool find_parent(
    const symbolt &symb,
    const irep_idt &base_name,
    irep_idt &identifier);

  bool get_component(
    const source_locationt &source_location,
    const exprt &object,
    const irep_idt &component_name,
    exprt &member);

  void new_temporary(const source_locationt &source_location,
                     const typet &,
                     const exprt::operandst &ops,
                     exprt &temporary);

  void new_temporary(const source_locationt &source_location,
                     const typet &,
                     const exprt &op,
                     exprt &temporary);

  /// N5008 [dcl.init.general]/9.1: whether value-initializing an object of
  /// this type zero-initializes it first -- a class whose selected default
  /// constructor is not user-provided, or a non-class type.
  bool value_initialization_zero_initializes(const typet &type);

  void static_and_dynamic_initialization();
  void do_not_typechecked();
  /// Clear the placeholders of implicitly-defined special members that
  /// were never odr-used (called once, after every body is elaborated).
  void clear_not_typechecked();
  void clean_up();
  void provide_stdlib_bodies();
  /// Give bodies, written in C++ and type-checked like any other, to
  /// functions that libc++ declares in its headers but defines only in its
  /// compiled library.
  void provide_library_source_models();
  exprt classic_num_put(const symbolt &accessor);

  /// Lay out the class's virtual bases after its non-virtual part (Itanium
  /// C++ ABI 2.4 II.3); their components are marked ID_C_virtual_base with
  /// the virtual base's class identifier.
  void append_virtual_bases(struct_typet &type, std::set<irep_idt> &vbases);

  void add_base_components(
    const struct_typet &from,
    const irep_idt &access,
    struct_typet &to,
    std::set<irep_idt> &vbases,
    bool is_virtual);

  bool cast_away_constness(const typet &t1,
                           const typet &t2) const;

  void do_virtual_table(const symbolt &symbol);

  /// The class's vtable struct `virtual_table::<class>`, created on first
  /// use (with the class's own virtual pointer, or embedding the primary
  /// base's table); returns its identifier.
  irep_idt ensure_virtual_table(
    const symbolt &symbol,
    struct_typet::componentst &components);

  /// Rebuild the bodies of the class's virtual-function thunks once the class
  /// is laid out (the `this' adjustments are base-subobject offsets).
  void finalize_virtual_thunks(const symbolt &symbol);

  /// Fill in the `\@vbase_offset::\<V\>' entries of the class's vtable objects
  /// (Itanium C++ ABI 2.5.2): the position of each virtual base in this
  /// complete object relative to the subobject owning the pointer.  Needs
  /// the final layout, so runs after padding.
  void set_virtual_base_offsets(const symbolt &symbol);

  /// The direct non-virtual bases of the class that have virtual bases: the
  /// ones with construction vtables (Itanium C++ ABI 2.6.2).
  std::vector<irep_idt>
  construction_vtable_bases(const irep_idt &class_id) const;

  /// For the base subobject \p base_id of the complete object \p symbol:
  /// each virtual pointer of the subobject with the address of the
  /// construction vtable (`virtual_table::X\@B\@D') to hold while the base is
  /// constructed or destroyed.
  std::vector<std::pair<struct_typet::componentt, exprt>>
  construction_vtable_installs(const symbolt &symbol, const irep_idt &base_id)
    const;

  /// Build (or rebuild) the body of the thunk \p thunk that a virtual
  /// function \p target (a component of \p derived) is entered through when
  /// called on the base subobject of class \p base_class: adjust `this' from
  /// the base subobject to the derived object and call \p target directly.
  /// The adjustment is the offset of the base subobject in \p derived's
  /// layout (Itanium C++ ABI 2.5.3 non-virtual thunk); a base sharing the
  /// derived class's virtual pointer is at offset 0.
  void build_virtual_thunk_body(
    symbolt &thunk,
    const irep_idt &target,
    const typet &target_type,
    const irep_idt &base_class,
    const struct_typet &derived);

  /// The body of the thunk \p thunk: subtract \p base_off (the offset of
  /// the base subobject the thunk is called on) from `this' and call
  /// \p target directly.
  void build_this_adjusting_thunk_body(
    symbolt &thunk,
    const irep_idt &target,
    const typet &target_type,
    const std::optional<mp_integer> &base_off);

  /// N5008 [class.mi]/4, [class.virtual]/2: a virtual table object for each
  /// base class subobject occurring more than once in the lattice (see
  /// add_base_components), with the final overriders of that subobject.
  void do_repeated_subobject_virtual_tables(const symbolt &symbol);

  /// The name of the virtual table object of \p most_derived for the
  /// repeated base class subobject whose virtual pointer is \p vtptr.
  static irep_idt repeated_subobject_vtable_name(
    const irep_idt &most_derived,
    const struct_typet::componentt &vtptr);

  /// Itanium C++ ABI 2.4: the primary base class of a dynamic class is its
  /// first non-virtual dynamic base class in declaration order; the class
  /// shares the primary base's virtual pointer (and vtable) instead of adding
  /// one.  Returns the primary base's class identifier, or an empty id when
  /// \p class_id has none (its dynamic bases, if any, are all virtual).
  irep_idt primary_base(const irep_idt &class_id) const;

  /// The `@vtable_pointer` component through which virtual functions of
  /// class \p class_id are dispatched: the class's own pointer, or that of
  /// the primary-base chain it shares.  Empty when the class is not dynamic.
  irep_idt vtable_pointer_component(const irep_idt &class_id) const;

  /// The vtable structs on the primary-base chain of \p class_id, most
  /// derived first: `virtual_table::C` for C = class_id (if it declares
  /// virtual functions), then its primary base, and so on.  Each vtable
  /// struct embeds the next one as its first member `@base`.
  std::vector<irep_idt> vtable_chain(const irep_idt &class_id) const;

  /// The address to store into the vtable pointer component \p vtptr of a
  /// complete object of class \p most_derived: the (possibly embedded) vtable
  /// object `virtual_table::T@most_derived` of the most derived class T of
  /// \p most_derived's hierarchy whose vtable chain reaches the pointer's
  /// vtable struct.  Nil when no such object exists.
  exprt vtable_pointer_value(
    const symbolt &most_derived,
    const struct_typet::componentt &vtptr) const;

  // we need to be able to delay the typechecking
  // of method bodies to handle methods with
  // bodies in the class definition
  struct method_bodyt
  {
  public:
    method_bodyt(
      symbolt *_method_symbol,
      const template_mapt &_template_map,
      const instantiation_stackt &_instantiation_stack):
      method_symbol(_method_symbol),
      template_map(_template_map),
      instantiation_stack(_instantiation_stack)
    {
    }

    symbolt *method_symbol;
    template_mapt template_map;
    instantiation_stackt instantiation_stack;
    /// see lookup_source_limit
    bool limit_lookup_to_source_order = false;
  };

  /// N5008 [basic.lookup.unqual]/4, [basic.lookup.argdep]/4,
  /// [class.mem.general]/7: a name is visible only after its declaration;
  /// the body of a member function defined in its (non-template) class is
  /// looked up as if it followed the class definition.  The front end
  /// converts function bodies at the end of the translation unit; while it
  /// converts the body of a function whose declaration has the source order
  /// (ID_C_source_order, assigned by the parser) L, namespace-scope
  /// functions declared with a larger source order are excluded from
  /// unqualified (and argument-dependent) function lookup.
  std::size_t lookup_source_limit = std::numeric_limits<std::size_t>::max();
  /// the source order of the first declaration of each function
  std::unordered_map<irep_idt, std::size_t> source_order;
  /// the source order of the definition of each function
  std::unordered_map<irep_idt, std::size_t> definition_source_order;
  void note_source_order(
    const irep_idt &identifier,
    const irept &declaration,
    bool is_definition)
  {
    const std::size_t order = declaration.get_size_t(ID_C_source_order);
    if(order == 0)
      return;
    source_order.emplace(identifier, order);
    if(is_definition)
      definition_source_order[identifier] = order;
  }

  typedef std::list<method_bodyt> method_bodiest;
  std::set<irep_idt> methods_seen;

  // N5008 [temp.inst]/4, /11: a function template specialization
  // instantiated only to test a candidate's viability during overload
  // resolution (a converting constructor template tried for a
  // user-defined conversion) must not have its BODY instantiated unless
  // the candidate is selected -- the body may be ill-formed for those
  // arguments, and a conforming compiler never sees it.  Such instances
  // are recorded here; their queued bodies are held back until a
  // reference to them appears in some converted body, and dropped
  // silently at the end if none does.
  std::set<irep_idt> speculative_instances;

  /// constexpr objects of array or class type: the declarator converter
  /// keeps them real objects (not macros), but their initializers are still
  /// manifestly constant-evaluated (N5008 [dcl.constexpr]/6, [expr.const]).
  std::set<irep_idt> constexpr_objects;

  /// N5008 [expr.context]/1, [basic.def.odr]/5, [temp.inst]/4: a function
  /// named in an unevaluated operand (the operand of decltype, sizeof,
  /// noexcept, a non-polymorphic typeid) is not odr-used, so a function
  /// template specialization it names has its declaration instantiated but
  /// not its definition.  Counts the nesting of unevaluated operands being
  /// type-checked; a specialization instantiated while it is non-zero is
  /// recorded in speculative_instances.
  unsigned unevaluated_operand_depth = 0;

  class unevaluated_operandt
  {
  public:
    explicit unevaluated_operandt(cpp_typecheckt &_cpp_typecheck)
      : cpp_typecheck(_cpp_typecheck)
    {
      ++cpp_typecheck.unevaluated_operand_depth;
    }
    ~unevaluated_operandt()
    {
      --cpp_typecheck.unevaluated_operand_depth;
    }

  private:
    cpp_typecheckt &cpp_typecheck;
  };
  method_bodiest held_back_bodies;
  bool release_referenced_held_back_bodies();
  void drop_unreferenced_held_back_bodies();

  // True while instantiate_template converts a member FUNCTION
  // template instance; gates the concretized-pack-pattern fallback in
  // typecheck_compound_declarator ([temp.variadic]/5), which must not
  // fire during CLASS instantiation.
  bool instantiating_member_function_template = false;
  method_bodiest method_bodies;

  // Deferred method bodies for lazy template elaboration.
  std::map<irep_idt, method_bodyt> deferred_method_bodies;
  /// The non-user-provided defaulted members deferred until odr-used
  /// ([dcl.fct.def.default]/5); a conversion of one of them happens because
  /// it is odr-used, so a failure is an error ([dcl.fct.def.delete]/2)
  std::set<irep_idt> odr_use_defined_defaulted_members;

  /// Constructors (and other member functions) that are odr-used as the target
  /// of a constructor member-initializer.  A synthesized constructor's base- or
  /// member-subobject initializer is lowered to a class-name constructor call
  /// that is only resolved to the concrete overload during goto conversion, so
  /// the resolved callee does not appear as a symbol reference in the stored
  /// body and the deferred-body drain's reference scan cannot see it.  We
  /// record such callees here (at the point of resolution in
  /// typecheck_member_initializer) so the drain still elaborates them
  /// ([temp.inst]/4: an implicitly-instantiated member that is odr-used must be
  /// instantiated).
  std::set<irep_idt> odr_used_by_member_initializer;

  void add_method_body(symbolt *_method_symbol);
  void
  bind_class_instance_parameters(const symbolt &class_sym, template_mapt &map);

  /// Static member symbols whose initializers are deferred until
  /// after the class body is fully declared.
  /// In-class initializers of static data members that could not be
  /// type-checked during member declaration and are re-attempted once the
  /// class is complete (N5008 [basic.scope.class]: earlier-declared member
  /// names, e.g. class-local typedefs, must be in scope for the
  /// initializer): (member symbol, enclosing class symbol) pairs.
  std::vector<std::pair<irep_idt, irep_idt>> deferred_static_initializers;

  /// Depth of typecheck_compound_body nesting: while positive, some class is
  /// being elaborated (and is incomplete); see convert_function.
  unsigned compound_body_depth = 0;
  bool suppress_elaborate = false;

  /// When true, typecheck_template_args does NOT expand pack-expansion
  /// template arguments ([temp.variadic]).  Set while matching a partial
  /// class-template specialization against actual arguments
  /// (disambiguate_template_classes), where the specialization's own
  /// parameter packs must be matched/deduced rather than substituted with an
  /// (unrelated) enclosing instantiation's pack.
  bool disable_template_arg_pack_expansion = false;
  /// true while the type of an alias-declaration (`using T = ...;') is
  /// typechecked; GCC ignores a GNU type attribute applied to a class type
  /// there, but honours it in a typedef
  bool in_alias_declaration = false;

  /// When true, suppress_elaborate is ignored. Used during constexpr
  /// member evaluation to ensure referenced templates can be
  /// instantiated even when nested typecheck_compound_body calls
  /// set suppress_elaborate=true.
  bool force_elaborate = false;

  /// True while draining the deferred method-body queue
  /// (typecheck_method_bodies): the function bodies converted here are not in
  /// a constant-evaluation context (unlike a call in `main` that the constexpr
  /// evaluator folds), so a function-template call resolved here materialises a
  /// real instance whose parameter pack must be expanded to the deduced arity
  /// ([temp.variadic]).  Used to enable type-internal pack expansion for
  /// directly-deduced packs without disturbing the constant-folding of the
  /// same call shape in an eagerly-converted (e.g. main) body.
  bool instantiating_deferred_body = false;

  bool builtin_factory(const irep_idt &) override;

  // types

  void typecheck_type(typet &) override;

  bool is_concept_name(const cpp_namet &name);
  void add_type_constraint(
    exprt &parameter,
    const irep_idt &concept_name,
    const cpp_namet &parameter_name,
    const irept &constraint_args);

  cpp_scopet &typecheck_template_parameters(
    template_typet &type);

  void typecheck_compound_type(struct_union_typet &) override;
  void check_fixed_size_array(typet &type);
  void typecheck_enum_type(typet &type);

  // determine the scope into which a tag goes
  // (enums, structs, union, classes)
  cpp_scopet &tag_scope(
    const irep_idt &_base_name,
    bool has_body,
    bool tag_only_declaration);

  void expand_folds_over_template_packs(
    irept &body,
    const template_typet &template_type,
    bool single_pack_too = false);
  bool out_of_class_definition_constraints_match(
    const template_typet &decl_tt,
    const template_typet &class_tt,
    const cpp_declarationt &md);
  void remove_empty_function_parameter_pack(
    const symbolt &template_symbol,
    cpp_declarationt &new_decl);
  /// Whether the trailing requires-clause of the non-template member
  /// function \p candidate of a class template specialization is satisfied
  /// (true when there is none or it cannot be decided).
  bool member_constraints_satisfied(const exprt &candidate);
  std::unordered_map<irep_idt, bool> member_constraint_cache;
  /// Expand the fold-expressions over the pack named \p short_name in
  /// \p node, for the elements \p pack_args ([expr.prim.fold]/2-3).
  static void expand_folds_over_pack(
    irept &node,
    const std::string &short_name,
    const std::vector<exprt> &pack_args);
  bool has_subobject_without_default_constructor(const struct_typet &type);
  void expand_trailing_return_packs(
    typet &final_type,
    const std::map<irep_idt, std::size_t> &pack_counts);
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
  void typecheck_compound_body(struct_union_typet &) override
  {
    UNREACHABLE;
  }
  void typecheck_enum_body(symbolt &symbol, bool underlying_defaulted);
  void typecheck_method_bodies();

  /// N5008 [temp.inst]/5 + [expr.const]: instantiate (convert) the
  /// definition of a deferred member function NOW, because its value is
  /// needed for constant evaluation (e.g. a constexpr `_S_gcd` used in a
  /// DEFAULT TEMPLATE ARGUMENT of a member alias like std::chrono's
  /// `__divide`, evaluated while the deferred drain has not yet reached
  /// it).  Looks the identifier up in deferred_method_bodies and the
  /// method_bodies queue; converts under the entry's recorded template
  /// map.  Returns true if a conversion was performed.
  bool convert_deferred_method_now(const irep_idt &identifier);

  /// Shared preprocessing for a deferred method body about to be converted
  /// ([temp.inst]/1, [temp.variadic]/5,7); used by both drains in
  /// typecheck_method_bodies.
  void prepare_deferred_method_body(symbolt &method_symbol);
  void complete_constructor_template_initializers(symbolt &method_symbol);
  cpp_declarationt inherited_constructor_declaration(
    const symbolt &symbol,
    const exprt &base,
    const symbolt &base_symbol,
    const code_typet &constructor_type) const;
  static bool inherited_constructor_is_hidden(
    const cpp_declaratort &declarator,
    const irep_idt &class_tag,
    const struct_typet::componentst &components);
  codet static_local_initialization(
    const symbolt &symbol,
    const codet &initialization);
  /// Collapse zero-length pack expansions (N5008 [temp.variadic]/7) in
  /// template-argument lists within an instantiated function-template body,
  /// using the empty packs recorded in the current `template_map`.
  void remove_empty_pack_expansion_args(exprt &body);
  void typecheck_contracts();
  void typecheck_compound_bases(struct_typet &type);
  /// N5008 [temp.variadic]/7: drop template arguments of \p name that are pack
  /// expansions over a parameter pack empty in the current instantiation (per
  /// template_map.pack_size_map), e.g. rewrite `X<_Tail...>` to `X<>`.  No-op
  /// when no instantiation is in progress (empty pack_size_map).
  void drop_empty_pack_template_args(irept &name);
  void add_anonymous_members_to_scope(const symbolt &struct_union_symbol);

  void move_member_initializers(
    irept &initializers,
    const code_typet &type,
    exprt &value);

  static bool has_const(const typet &type);
  static bool has_volatile(const typet &type);
  static bool has_auto(const typet &type);

  void typecheck_member_function(
    const symbolt &compound_symbol,
    struct_typet::componentt &component,
    irept &initializers,
    const typet &method_qualifier,
    exprt &value);

  void add_this_to_method_type(
    const symbolt &compound_symbol,
    code_typet &method_type,
    const typet &method_qualifier);

  // for function overloading
  irep_idt function_identifier(const typet &type);

  void zero_initializer(
    const exprt &object,
    const typet &type,
    const source_locationt &source_location,
    exprt::operandst &ops);

  // code conversion
  void typecheck_code(codet &) override;
  void typecheck_return(code_frontend_returnt &) override;
  void typecheck_try_catch(codet &);
  void typecheck_member_initializer(codet &);
  void typecheck_decl(codet &) override;
  bool expression_statement_is_declaration(codet &code);
  void record_constexpr_object_value(
    const symbolt &symbol,
    const cpp_declaratort &declarator);
  void typecheck_block(code_blockt &) override;
  void typecheck_ifthenelse(code_ifthenelset &) override;
  void typecheck_while(code_whilet &) override;
  void typecheck_switch(codet &) override;

  const struct_typet &this_struct_type();

  /// The destructor call for \p object; \p base_subobject when it is a base
  /// subobject destroyed by a derived class's destructor (the base-object
  /// destructor of a class with virtual bases is then requested).
  std::optional<codet> cpp_destructor(
    const source_locationt &source_location,
    const exprt &object,
    bool force_direct = true,
    bool base_subobject = false);

  // expressions
  /// Whether \p expr is `&C::m' (an unparenthesized qualified-id) in a
  /// scope that has a `this' ([expr.unary.op]/4).
  bool is_qualified_member_address(const exprt &expr);

  std::optional<irep_idt> naming_class_of(const cpp_namet &name);

  /// Whether the (substituted) constraint \p constraint is satisfied
  /// ([temp.constr.op], [temp.constr.atomic]); empty when the front end
  /// cannot evaluate it.
  /// The satisfaction of a concept's constraint-expression \p constraint
  /// ([temp.constr.normal], [temp.constr.op]), as a bool expression.
  exprt constraint_satisfaction(const exprt &constraint);
  /// Convert the initializer of the concept variable \p symbol, its
  /// constraint-expression ([temp.constr.atomic]/3, [temp.constr.op]).
  void convert_concept_initializer(symbolt &symbol);
  std::optional<bool> evaluate_constraint(const exprt &constraint);
  void explicit_typecast_ambiguity(exprt &);
  void unary_operand_typecast_ambiguity(exprt &);
  void typecheck_expr_main(exprt &) override;
  /// Phase 1B target-typet overload of \ref typecheck_expr_main; the
  /// target is currently discarded.  See
  /// `doc/architectural/cpp-frontend-plan-target-type-threading.md`.
  void typecheck_expr_main(exprt &, const target_typet &);

  /// C++20 [expr.prim.req.simple]: returns true iff \p op is a valid
  /// expression for the current (substituted) requirement-parameters.  Any
  /// failure -- including a typecheck error that is reported without throwing
  /// (e.g. member access on a non-class type) -- is converted into a soft
  /// `false` per [expr.prim.req.general]/5, and the error count is restored so
  /// the enclosing translation unit is not failed.
  bool requirement_expression_is_valid(exprt op);

  /// C++20 [expr.prim.req.compound]/1: returns true iff the
  /// compound-requirement \p expr (`{ E } noexcept_opt -> C_opt`) is
  /// satisfied: \c E is a valid expression and, if a return-type-requirement
  /// \c C is present, \c C is satisfied by `decltype((E))`.  Soft failure per
  /// [expr.prim.req.general]/5.
  bool compound_requirement_is_satisfied(const exprt &expr);
  bool
  is_trivially_copyable_type(const typet &type, bool want_trivial, int depth);

  /// N5008 [except.spec]/8: whether default-initializing an object of
  /// \p type calls only non-throwing functions (the construction itself
  /// is assumed to be valid).
  bool default_construction_is_nothrow(const typet &type, int depth);

  /// N5008 [class.prop], [class.virtual]/1, [class.dtor]/9,
  /// [dcl.init.aggr]/1: the class property named by the GCC/Clang type
  /// trait \p trait (`__is_empty', `__is_polymorphic', ...) for type \p t
  bool class_property(const irep_idt &trait, const typet &t);
  bool select_pack_element(typet &type);
  bool has_trivial_destructor(const typet &type, int depth);
  bool is_destructible_type(const typet &type, int depth);
  bool has_trivial_special_member(
    const typet &type,
    const irep_idt &kind,
    int depth,
    bool implicit_suffices = false);
  bool has_unique_object_representations(const typet &type, int depth);
  bool is_trivially_equality_comparable(const typet &type, int depth);

  bool out_of_line_definition_matches(
    const symbolt &member,
    const cpp_declarationt &def,
    const cpp_template_args_tct *class_args);
  void adopt_definition_parameter_names(
    symbolt &member,
    const cpp_declarationt &def);

  void rename_template_parameters_to_declaration(
    irept &node,
    const template_typet &def_tt,
    const template_typet &class_tt,
    const template_typet &decl_tt);

  bool member_template_parameters_match(
    const irept &decl_params,
    const template_typet &decl_tt,
    const template_typet &class_tt,
    const irept &def_params,
    const template_typet &def_tt);

  /// N5008 [expr.prim.req.general]/2-3: bind a requirement-parameter of a
  /// requires-expression (`requires(T a) { ... }`) as a local symbol of the
  /// current (instantiation) scope, of the substituted type \p type.  Each
  /// binding is a distinct symbol: the parameters are notation local to
  /// their requires-expression, and a shared per-name symbol was overwritten
  /// by a nested evaluation of another concept using the same parameter name
  /// (libstdc++'s `__i` in weakly_incrementable and in every iterator
  /// concept), so `++__i` was checked against the wrong type.
  void bind_requires_parameter(const irep_idt &name, const typet &type);

  void typecheck_expr_member(exprt &) override;
  void typecheck_expr_ptrmember(exprt &) override;
  void typecheck_expr_throw(exprt &);
  void typecheck_function_expr(exprt &, const cpp_typecheck_fargst &);
  void typecheck_expr_cpp_name(exprt &, const cpp_typecheck_fargst &);
  void typecheck_expr_member(exprt &, const cpp_typecheck_fargst &);
  void typecheck_expr_ptrmember(exprt &, const cpp_typecheck_fargst &);
  void typecheck_cast_expr(exprt &);
  void typecheck_expr_trinary(if_exprt &) override;
  void typecheck_expr_binary_arithmetic(exprt &) override;
  void typecheck_expr_explicit_typecast(exprt &);
  void typecheck_expr_explicit_constructor_call(exprt &);

  /// C++17 class template argument deduction ([over.match.class.deduct]).
  /// If \p class_template_name is written without template arguments and names
  /// a class template, deduce the template arguments from the (not necessarily
  /// type-checked) initializer expressions \p args and return the resulting
  /// type-checked class type (e.g. `Box<int>`); otherwise return {}.
  /// \p copy_initialization: `C x = e' ([over.match.copy]/1.1), where the
  /// notional constructors formed from explicit constructors are not
  /// candidates ([over.match.class.deduct]/5).
  std::optional<typet> deduce_class_template_arguments(
    const cpp_namet &class_template_name,
    const std::vector<exprt> &args,
    bool copy_initialization = false);
  void typecheck_expr_address_of(exprt &) override;
  /// Phase 1B target-typet overload of \ref typecheck_expr_address_of;
  /// the target is currently discarded.  Phase 2 of the target-type-
  /// threading refactor will use this to deduce
  /// [temp.deduct.funcaddr]/1 template arguments forward.
  void typecheck_expr_address_of(exprt &, const target_typet &);
  void typecheck_expr_dereference(exprt &) override;
  void typecheck_expr_function_identifier(exprt &) override;
  void typecheck_expr_reference_to(exprt &);
  void typecheck_expr_this(exprt &);
  void typecheck_expr_typeid(exprt &);
  void typecheck_expr_new(exprt &);
  void typecheck_expr_sizeof(exprt &) override;
  void typecheck_expr_is_invocable(exprt &expr);
  const symbolt &virtual_dispatch_thunk(const irep_idt &function_identifier);
  void typecheck_braced_argument_elements(exprt &init_list);
  std::optional<typet> builtin_common_type(
    const irep_idt &base_template,
    const std::vector<typet> &types,
    const source_locationt &source_location);
  bool implicit_pod_assignment_call(side_effect_expr_function_callt &expr);
  void user_defined_numeric_literal(side_effect_expr_function_callt &expr);
  /// The closure member holding a lambda's captured `this'
  static constexpr const char *lambda_this_capture = "__cbmc_lambda_this";
  void rewrite_lambda_this_uses(
    irept &body,
    const std::set<irep_idt> &member_functions,
    const std::set<irep_idt> &class_names = {});
  bool bind_requires_parameter_pack(const irep_idt &name, const typet &type);
  void expand_requires_parameter_packs(exprt &expr);
  void expand_requires_parameter_packs_in_type(irept &type);
  exprt requires_parameter_pack_element(
    const irep_idt &name,
    const typet &element_type);
  /// The element symbols of each requires-expression parameter pack bound by
  /// bind_requires_parameter_pack, by the parameter's name.
  std::map<irep_idt, std::vector<exprt>> requires_parameter_packs;
  /// \p with_requires_parameters: also expand requires-expression
  /// parameter packs (requires_parameter_packs), while a requirement is
  /// checked.
  void expand_type_pack_arguments(
    exprt &arguments,
    bool with_requires_parameters = false);
  std::vector<typet> builtin_trait_type_args(const exprt &expr);
  void throw_if_incomplete_dependency(const exprt &expr);
  void complete_type_operand(exprt &expr);
  std::optional<struct_exprt>
  zero_struct_value(const typet &type, const source_locationt &loc);
  static void set_struct_member_value(
    struct_exprt &value,
    const struct_typet &struct_type,
    const struct_union_typet::componentt &component,
    exprt member_value);
  bool convert_explicit_instantiation(cpp_declarationt &declaration);
  bool is_lvalue_expression(const exprt &expr) const;
  void typecheck_expr_alignof(exprt &) override;
  void typecheck_expr_lambda(exprt &);
  void typecheck_expr_delete(exprt &);
  void typecheck_expr_side_effect(side_effect_exprt &) override;
  void typecheck_side_effect_assignment(side_effect_exprt &) override;
  void typecheck_side_effect_inc_dec(side_effect_exprt &);
  void typecheck_expr_typecast(exprt &) override;
  void typecheck_expr_index(exprt &) override;
  void typecheck_expr_rel(binary_relation_exprt &) override;
  void typecheck_expr_comma(exprt &) override;
  void typecheck_expr_unary_arithmetic(exprt &) override;

  void
  typecheck_function_call_arguments(side_effect_expr_function_callt &) override;
  exprt typecheck_deferred_default_argument(const exprt &deferred);

  void instantiate_generic_lambda(side_effect_expr_function_callt &);

  bool operator_is_overloaded(exprt &);
  bool nonmember_operator_is_better(
    const exprt::operandst &operands,
    const irep_idt &member,
    const irep_idt &nonmember);
  bool rewritten_comparison_candidate(exprt &expr);
  bool overloadable(const exprt &);

  void add_implicit_dereference(exprt &);

  void typecheck_side_effect_function_call(
    side_effect_expr_function_callt &) override;

  /// Phase 1B target-typet overload of
  /// \ref typecheck_side_effect_function_call; the target is
  /// currently discarded.  Phase 2 will use this to thread the
  /// target through to per-argument deduction.
  void typecheck_side_effect_function_call(
    side_effect_expr_function_callt &,
    const target_typet &);

  /// Deduce template-function arguments from the target function type
  /// per N5008 [temp.deduct.funcaddr]/1:
  ///
  ///   > Template arguments can be deduced from the type specified
  ///   > when taking the address of an overload set.  If there is
  ///   > a target, the function template's function type and the
  ///   > target type are used as the types of P and A, and the
  ///   > deduction is done as described in 13.10.3.6.
  ///
  /// Context: overload resolution for a function call whose callee
  /// is a non-template ordinary function and whose corresponding
  /// parameter type is a pointer-to-function.  Any argument of the
  /// form `&f` or plain `f` (implicit function-to-pointer per
  /// [conv.func]) where `f` names a function template is deduced
  /// against the parameter's pointed-to code type, so that the
  /// template argument is determined by the target rather than by
  /// the argument alone (the argument alone has no fargs to
  /// deduce from and would fail in the default resolve path).
  ///
  /// The function is a no-op when every argument is already
  /// typed; it runs as a "probe + retry" because CBMC's overall
  /// pipeline typechecks arguments before resolving the callee.
  /// Once a proper target-type threading is in place (roadmap
  /// §3.3), the probe step becomes redundant and this helper
  /// collapses into the main path.
  ///
  /// [temp.deduct.funcaddr]/1: deduce template arguments for a
  /// function-template name being matched against a target
  /// pointer-to-function type.  Returns a typed `address_of` expr
  /// on success, or nil on substitution failure
  /// (silent per [temp.deduct]/8).  The \p source_location is
  /// attached to the synthesised `address_of`.
  ///
  /// \p name_or_addressof is the source argument: either a bare
  /// `cpp_name` (implicit function-to-pointer per [conv.func]/1)
  /// or an explicit `&cpp_name` `address_of`.  In either case the
  /// resulting expression is a typed `address_of` that the caller
  /// can substitute for the original.
  exprt deduce_funcaddr_against_target(
    const exprt &name_or_addressof,
    const typet &target_fn_pointer_type);

  void typecheck_method_application(side_effect_expr_function_callt &);

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

  /// A base class subobject within a flattened class layout: the path of
  /// base classes that leads to it (from a direct base of the derived class,
  /// or from the virtual base containing it), its offset, and the virtual
  /// base it lies in (empty for the non-virtual part).
  struct base_subobjectt
  {
    std::vector<irep_idt> path;
    mp_integer offset;
    irep_idt virtual_base;
  };

  /// The subobjects of class \p base in an object of class \p derived
  /// ([class.mi]/4), in layout order; a base class without storage (an empty
  /// base) has none.
  std::vector<base_subobjectt>
  base_subobjects(const struct_typet &derived, const irep_idt &base);

  std::optional<mp_integer>
  base_subobject_offset(const typet &derived, const typet &base);
  bool standard_conversion_pointer_to_member(
    const exprt &expr, const typet &type, exprt &new_expr);

  bool standard_conversion_boolean(
    const exprt &expr, exprt &new_expr) const;

  bool standard_conversion_sequence(
    const exprt &expr, const typet &type, exprt &new_expr, unsigned &rank);

  bool user_defined_conversion_sequence(
    const exprt &expr, const typet &type, exprt &new_expr, unsigned &rank);

  /// Phase 4B: per [temp.deduct.conv]/1, attempt to deduce template
  /// arguments for a conversion-function template by unifying the
  /// template's return type (P) with the destination type (A).
  /// Called from `user_defined_conversion_sequence` after the
  /// non-template cast-operator loop.  Iterates template cast
  /// operators of the source class, runs SFINAE-guarded deduction
  /// per [temp.deduct]/8, applies [temp.deduct.partial]/3.2 partial
  /// ordering across deduction survivors when more than one is
  /// viable, then instantiates the unique most-specialised match.
  /// Per [over.ics.user]/3 the second standard conversion sequence
  /// must be Exact Match.
  ///
  /// Returns `true` on a successful unambiguous deduction, with
  /// `new_expr` set to the typechecked conversion expression and
  /// `rank` incremented by the second standard conversion's rank.
  /// Returns `false` if no candidate is found, deduction fails for
  /// every candidate, or partial ordering cannot pick a unique
  /// most-specialised candidate (genuine ambiguity).
  bool deduce_conversion_template(
    const exprt &expr,
    const typet &to,
    exprt &new_expr,
    unsigned &rank);

  /// Phase 4B: companion to `deduce_conversion_template` for
  /// reference-binding contexts ([dcl.init.ref], handled in
  /// `reference_binding`).  When the destination type is a
  /// reference, the shared deduction helper is invoked with the
  /// reference type as `to`; [temp.deduct.conv]/2 + /4 strip the
  /// references on P and A before deduction.  After instantiation
  /// the post-conversion check is `reference_compatible` rather
  /// than `standard_conversion_sequence` per [over.match.ref].
  bool deduce_conversion_template_for_reference(
    const exprt &expr,
    const reference_typet &reference_type,
    exprt &new_expr,
    unsigned &rank);

  /// Phase 4B core helper.  Iterates template cast operators of the
  /// source class of `expr`, runs SFINAE-guarded [temp.deduct.conv]
  /// deduction against `to`, applies partial ordering across
  /// survivors, and instantiates the unique most-specialised
  /// candidate.  Both value and reference destination types are
  /// accepted; the deduction transformations handle the difference.
  ///
  /// Returns the instantiated function symbol on success, or
  /// `nullptr` on no-candidate / total deduction failure / genuine
  /// ambiguity.  The caller is responsible for building the call
  /// expression and validating the post-instantiation conversion
  /// sequence appropriate to the calling context.
  /// per class (tag identifier): the conversion function templates declared
  /// in it, for find_template_conversion_specialisation
  std::unordered_map<irep_idt, std::vector<irep_idt>>
    template_conversion_candidates;

  const symbolt *
  find_template_conversion_specialisation(const exprt &expr, const typet &to);

  /// [temp.deduct.partial]/3.2: in conversion-function context,
  /// returns `true` iff conversion-function template F is at-least-
  /// as-specialised as G when their return types serve as the P/A
  /// pair.  Implemented as: deduce F's parameters from G's
  /// (transformed) return type and require all parameters to be
  /// bound.  /5 (drop reference) and /7 (drop top-level cv) are
  /// applied first.
  bool conversion_template_at_least_as_specialised(
    const cpp_declarationt &F,
    const cpp_declarationt &G,
    const irep_idt &F_scope_id,
    const irep_idt &G_scope_id);

  /// N5008 [temp.func.order] + [temp.deduct.partial]/3.1: returns true if
  /// function template F is at-least-as-specialised as G when their
  /// function parameter-type-lists serve as the P/A pairs.  Implemented as:
  /// deduce G's template parameters from F's (transformed) parameter types,
  /// position by position, and require all of G's parameters to be bound.
  /// /5 (drop reference) and /7 (drop top-level cv) are applied to each
  /// pair first.  F's template parameters are inert during the deduction
  /// because their identifiers carry F's scope prefix and are not in the
  /// template_map (the "transformed type" device).
  bool function_template_at_least_as_specialised(
    const cpp_declarationt &F,
    const cpp_declarationt &G,
    const irep_idt &F_scope_id,
    const irep_idt &G_scope_id);

  /// N5008 [temp.spec.partial.order]/1 + [temp.func.order]: returns true if
  /// class-template partial specialisation F is at-least-as-specialised as
  /// G.  Each specialisation is viewed as the function template
  /// `template<params> void f(X<args>)` and the argument patterns are
  /// compared position by position by deducing G's template parameters
  /// from F's (inert) patterns; every G parameter occurring in the compared
  /// patterns must be deduced.  Expression (non-type) arguments compare
  /// structurally unless G's is a bare template parameter.
  bool partial_specialization_at_least_as_specialised(
    const cpp_declarationt &F,
    const cpp_declarationt &G,
    const irep_idt &G_scope_id);

  /// The symbol of the already-materialised specialization of function
  /// template \p template_symbol for \p template_args, or the empty
  /// identifier when it has not been instantiated yet.  Mirrors the
  /// "instance already" lookup in instantiate_template.
  irep_idt existing_function_template_instance(
    const symbolt &template_symbol,
    const cpp_template_args_tct &template_args);

  bool reference_related(const exprt &expr, const reference_typet &type) const;

  bool reference_compatible(
    const exprt &expr,
    const reference_typet &type,
    unsigned &rank,
    unsigned *cv_distance = nullptr) const;

  bool reference_binding(
    exprt expr,
    const reference_typet &type,
    exprt &new_expr,
    unsigned &rank,
    unsigned *cv_distance = nullptr);

  bool implicit_conversion_sequence(
    const exprt &expr,
    const typet &type,
    exprt &new_expr,
    unsigned &rank,
    unsigned *cv_distance = nullptr);

  bool implicit_conversion_sequence(
    const exprt &expr, const typet &type, unsigned &rank);

  bool implicit_conversion_sequence(
    const exprt &expr, const typet &type, exprt &new_expr);

  bool explicit_conversion_function_to(
    const exprt &expr,
    const typet &to,
    exprt &new_expr);

  symbol_exprt initializer_list_backing_array(
    exprt::operandst elements,
    const array_typet &array_type,
    const source_locationt &source_location,
    bool constant,
    std::optional<exprt> &prefix);
  static exprt sequence_before(
    std::optional<exprt> prefix,
    exprt result,
    const source_locationt &source_location);
  bool brace_init_to_array_reference(
    const exprt &init_list,
    const pointer_typet &reference_type,
    exprt &result);

  /// Whether direct-list-initialization of \p type from the
  /// braced-init-list \p init_list (an ID_initializer_list expression)
  /// should use an initializer-list constructor with the list as a single
  /// argument ([over.match.list]/1 phase 1.1).  True iff the class has a
  /// non-explicit initializer-list constructor (its remaining parameters
  /// defaulted) that is *viable* for this list: every non-braced element
  /// is convertible to the initializer_list's element type.  When false,
  /// [over.match.list]/1 phase 1.2 applies (all constructors, with the
  /// elements of the list as the arguments).
  bool
  has_viable_init_list_constructor(const typet &type, const exprt &init_list);
  bool has_unary_constructor_template(const struct_tag_typet &class_type);

  /// Build the std::initializer_list<U> argument value for list-
  /// initialization of \p target_type from the braced-init-list
  /// \p init_list, per [over.match.list]/1 phase 1.1.  \p target_type
  /// must have a viable initializer-list constructor (see
  /// has_viable_init_list_constructor).  Returns a value (a struct_exprt
  /// {begin_pointer, size} backed by a freshly created static array of
  /// the converted elements) suitable as the single constructor
  /// argument, or {} if \p target_type has no such constructor or the
  /// element types could not be converted.
  std::optional<exprt>
  build_init_list_argument(const typet &target_type, const exprt &init_list);

  /// [stmt.return]/2 + [dcl.init.aggr]: aggregate initialization of the
  /// result object from a braced-init-list return operand; nullopt when
  /// the return type is not an aggregate for this list.
  std::optional<exprt>
  braced_return_aggregate_value(const typet &return_type, exprt &init_list);

  /// Build a std::initializer_list<E> value from a braced-init-list per N5008
  /// [dcl.init.list]/5 (synthesise a backing const E[N] array and refer to it).
  /// \p il_type must be a std::initializer_list<E> struct-tag type.
  /// The element type E of a std::initializer_list<E> specialization, read
  /// off its layout: the first non-static data member is the pointer to the
  /// first element ([support.initlist]; libstdc++ `_M_array`, libc++
  /// `__begin_`, MSVC `_begin`).  Nil when \p il_type is not such a layout.
  typet initializer_list_element_type(const struct_tag_typet &il_type);

  std::optional<exprt> build_initializer_list_value(
    const struct_tag_typet &il_type,
    const exprt &init_list);

  void reference_initializer(exprt &expr, const reference_typet &type);

  void implicit_typecast(exprt &expr, const typet &type) override;

  /// N5008 [conv.general]/4: the contextual conversion to bool (the
  /// condition of if/while/for, the operand of !, &&, ||, ?:, static_assert,
  /// noexcept) is the direct-initialization `bool t(e)', for which an
  /// EXPLICIT `operator bool()' is a candidate ([class.conv.fct]/2).  All
  /// callers of implicit_typecast_bool are such contexts.
  void implicit_typecast_bool(exprt &expr) override
  {
    ++contextual_bool_conversion;
    try
    {
      implicit_typecast(expr, bool_typet());
    }
    catch(...)
    {
      --contextual_bool_conversion;
      throw;
    }
    --contextual_bool_conversion;
  }
  unsigned contextual_bool_conversion = 0;

  /// N5008 [over.match.conv]/1: non-zero while converting the single
  /// initializer of a DIRECT-initialization of a non-class object (`T t(e)',
  /// `T(e)', `static_cast<T>(e)'), where explicit conversion functions are
  /// candidates too.  RAII guard: direct_initialization_contextt.
  unsigned direct_initialization = 0;
  class direct_initialization_contextt
  {
  public:
    explicit direct_initialization_contextt(cpp_typecheckt &_cpp_typecheck)
      : cpp_typecheck(_cpp_typecheck)
    {
      ++cpp_typecheck.direct_initialization;
    }
    ~direct_initialization_contextt()
    {
      --cpp_typecheck.direct_initialization;
    }

  private:
    cpp_typecheckt &cpp_typecheck;
  };

  void implicit_typecast_arithmetic(exprt &expr1, exprt &expr2) override;

  void implicit_typecast_arithmetic(exprt &expr) override;

  void get_bases(const struct_typet &type,
     std::set<irep_idt> &set_bases) const;

  void get_virtual_bases(const struct_typet &type,
     std::list<irep_idt> &vbases) const;

  bool subtype_typecast(const struct_typet &from, const struct_typet &to) const;

  bool base_publicly_accessible(
    const struct_typet &from,
    const struct_typet &to) const;

  /// Convert the class pointer \p expr to the base (or derived) class pointer
  /// type \p dest_type, adjusting it by the base subobject's offset.  A base
  /// reached through a VIRTUAL base is located through the vtable at run
  /// time unless \p static_virtual_base_offset asks for this class's own
  /// layout (the complete object's constructor/destructor).  With
  /// \p direct_base, \p dest_type's class is a direct (or virtual) base of
  /// \p expr's class, and a base class that also occurs as an indirect base
  /// ([class.mi]/3) designates the direct base subobject.
  void make_ptr_typecast(
    exprt &expr,
    const pointer_typet &dest_type,
    bool static_virtual_base_offset = false,
    bool direct_base = false);

  // the C++ typecasts

  bool const_typecast(
    const exprt &expr,
    const typet &type,
    exprt &new_expr);

  bool dynamic_typecast(
    const exprt &expr,
    const typet &type,
    exprt &new_expr);
  /// N5008 [expr.dynamic.cast]/9: the run-time check of a dynamic_cast
  /// (cpp_typecheck_dynamic_cast.cpp), resolved once every class is known
  exprt runtime_dynamic_cast(const exprt &check);
  static bool is_class_prvalue_temporary(const exprt &expr);
  std::optional<codet> subobject_unwind_destructor(const codet &code);
  void add_constructor_unwinding(codet &body);
  bool defaulted_comparison_elements(
    const symbolt &symbol,
    code_typet &function_type,
    const exprt &this_expr,
    std::vector<std::pair<exprt, exprt>> &elements);
  bool convert_to_comparison_category(
    const exprt &value,
    const typet &category,
    exprt &result);
  std::optional<code_blockt> defaulted_three_way_comparison(
    const symbolt &symbol,
    code_typet &function_type,
    const exprt &this_expr);
  void resolve_runtime_dynamic_casts(exprt &expr);
  void resolve_runtime_dynamic_casts();

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

  bool contains_cpp_name(const exprt &);

private:
  typedef std::list<irep_idt> dynamic_initializationst;
  dynamic_initializationst dynamic_initializations;
  bool disable_access_control;           // Disable protect and private
  /// Set when a class template instance is derived from itself
  /// ([class.derived.general]/2): that error is not recovered from, and the
  /// flag stays set -- an error in the instantiation of a class is not in the
  /// immediate context of a deduction ([temp.deduct.general]/9), so the
  /// program is ill-formed whatever context caused the instantiation.
  bool class_derived_from_itself = false;
  /// Destination type identifiers whose converting *template* constructor is
  /// currently being tried by `user_defined_conversion_sequence`'s
  /// template-constructor fallback.  Prevents unbounded recursion when a
  /// conversion to `T` would recursively require another conversion to the
  /// same `T`, while still permitting a *distinct* nested target conversion --
  /// e.g. evaluating `is_constructible<Wrap, X>` (which converts `X -> Wrap`)
  /// while already converting `X -> optional<Wrap>`.  A single boolean guard
  /// blocked that legitimate nested query, wrongly reporting the inner
  /// conversion (hence the trait) as false.
  std::set<irep_idt> template_conversions_in_progress;
  bool skip_typechecking_elaborate = false;
  /// N5008 [temp.inst]/4, [class.friend]/6-7: set while a friend function
  /// defined in a class template specialization is declared; its definition
  /// is instantiated only when it is odr-used, like a member's.
  bool defining_friend_of_template_instance = false;

  /// N5008 [temp.inst]/1: naming a class template specialization does NOT
  /// instantiate it; only a context requiring completeness ([temp.inst]/2)
  /// does.  The front end still instantiates on naming (resolve's TYPE
  /// branch) -- switching this off is the structural change towards the
  /// standard's rule; the completeness-requiring sites already elaborate on
  /// their own (object definitions, function-definition parameter and
  /// return types, derived-to-base deduction, functional casts, member
  /// access, sizeof, bases, conversions).  The environment variable
  /// CBMC_ELAB_ON_NAMING=0 exercises the on-use mode; see the round-162
  /// notes for the remaining failures (7 of ~1400 cbmc-cpp tests, all in the
  /// instantiation-context handling of member templates of partial
  /// specializations).
  bool elaborate_on_naming = getenv("CBMC_ELAB_ON_NAMING") == nullptr ||
                             std::string(getenv("CBMC_ELAB_ON_NAMING")) != "0";
  std::unordered_set<irep_idt> deferred_typechecking;
  std::unordered_set<irep_idt> functions_being_typechecked;

  /// Function bodies whose first conversion failed and that were re-queued
  /// for one retry at the end of the translation unit (see convert_function).
  std::unordered_set<irep_idt> body_conversion_retried;

  // Guards the C++20 parenthesized-aggregate-initialization reroute in
  // typecheck_side_effect_function_call against re-entry: the
  // constructor-first attempt inside the rerouted path goes through
  // cpp_constructor, whose synthesized `T(args)` call would otherwise
  // reroute again, recursing forever.
  std::set<irep_idt> paren_aggregate_in_progress;
  std::map<irep_idt, exprt> generic_lambda_map;
  /// Maps a lambda-expression's source location to the symbol name of its
  /// synthesised closure type ([expr.prim.lambda.closure]/1: each lambda has a
  /// unique closure type).  A lambda may be type-checked more than once (e.g.
  /// auto return type deduction), and the closure type must be identical each
  /// time, so it is created once and reused.
  std::map<std::string, irep_idt> lambda_closure_map;
  bool support_float16_type;

  /// Counter that is non-zero while type-checking an expression that
  /// is required to be a constant expression ([expr.const]): non-type
  /// template arguments, array bounds, enumerator and bit-field
  /// values, `static_assert` operands, `case` labels, and `constexpr`
  /// initializers (and inside `make_constant`).  The constexpr
  /// evaluator in `typecheck_side_effect_function_call` only folds
  /// calls while this is non-zero; ordinary run-time elaboration -- by
  /// far the bulk of the work -- therefore skips the (expensive)
  /// folding, which is unnecessary outside a constant-required
  /// context because such calls denote ordinary run-time invocations.
  unsigned constant_expression_context = 0;
  friend class sfinae_contextt;

  /// system-header declarations dropped because their type checking failed
  std::vector<std::string> dropped_system_items;
  void report_dropped_system_item(const cpp_itemt &item);

  /// Whether \p file is a standard-library / system header, whose
  /// constructs the front end tolerates failing on (the diagnostics are
  /// suppressed and the item or body is dropped rather than failing the
  /// translation unit).  Covers the usual install roots and a compiler's
  /// relative include root (`/usr/bin/../include/c++/v1` for libc++).
  static bool is_system_header_file(const std::string &file);
  void report_dropped_body(const symbolt &symbol, const char *reason);

  /// is_system_header_file, plus a compiler's relative include root
  /// (`/usr/bin/../include/c++/v1` for libc++).  Used where a failing
  /// LIBRARY BODY is tolerated (dropped with a warning instead of failing
  /// the translation unit); the narrower predicate stays in force for the
  /// end-of-unit re-conversion sweep, whose candidates are stdlib instances
  /// only and which must not touch bodies converted without the
  /// \#cpp_converted stamp (nested lambdas).
  static bool is_library_body_file(const std::string &file);

  /// True while instantiating a template that was referenced from within a
  /// constant-expression context (so its definition may have to be folded
  /// now).  N5008 [temp.point]/1, [temp.inst]/5: a `constexpr` specialization
  /// reached this way must be converted eagerly so the constant is foldable;
  /// one reached for an ordinary run-time call can instead be deferred to the
  /// clean method-body drain (where derived-to-base pack calls etc. resolve
  /// correctly).  Set by `non_constant_expression_contextt` from the
  /// suspended outer context; read by `cpp_declarator_convertert`.
  bool instantiating_for_constant_eval = false;

  /// RAII guard marking a constant-expression context for its lifetime.
  class constant_expression_contextt
  {
  public:
    explicit constant_expression_contextt(cpp_typecheckt &_cpp_typecheck)
      : cpp_typecheck(_cpp_typecheck)
    {
      ++cpp_typecheck.constant_expression_context;
    }
    ~constant_expression_contextt()
    {
      --cpp_typecheck.constant_expression_context;
    }

  private:
    cpp_typecheckt &cpp_typecheck;
  };

  /// RAII guard that suspends any constant-expression context for its
  /// lifetime.  Used while type-checking a function body: a constexpr
  /// call appearing as an ordinary statement/sub-expression of a body
  /// is a run-time invocation, even when the body is reached (e.g. via
  /// template instantiation) from within a constant-required context.
  /// The evaluator's own nested folding stays enabled because it
  /// recurses through `typecheck_side_effect_function_call` directly,
  /// not through `convert_function`.
  class non_constant_expression_contextt
  {
  public:
    explicit non_constant_expression_contextt(cpp_typecheckt &_cpp_typecheck)
      : cpp_typecheck(_cpp_typecheck),
        saved(_cpp_typecheck.constant_expression_context),
        saved_instantiating_for_constant_eval(
          _cpp_typecheck.instantiating_for_constant_eval)
    {
      // Whether the enclosing (now-suspended) context was constant-required
      // tells `cpp_declarator_convertert` whether a `constexpr` specialization
      // reached during this instantiation must be converted eagerly (foldable
      // now) or may be deferred as an ordinary run-time definition.
      cpp_typecheck.instantiating_for_constant_eval =
        cpp_typecheck.constant_expression_context > 0;
      cpp_typecheck.constant_expression_context = 0;
    }
    ~non_constant_expression_contextt()
    {
      cpp_typecheck.constant_expression_context = saved;
      cpp_typecheck.instantiating_for_constant_eval =
        saved_instantiating_for_constant_eval;
    }

  private:
    cpp_typecheckt &cpp_typecheck;
    unsigned saved;
    bool saved_instantiating_for_constant_eval;
  };

  /// Counter > 0 while applying explicit template arguments to a candidate
  /// during overload resolution (`apply_template_args`).  In that context a
  /// template-argument *kind* mismatch -- e.g. a non-type argument supplied
  /// for a type parameter, as when resolving the by-index
  /// `std::get<0>(tuple<...>)` also matches the by-type
  /// `std::get<T>(pair<...>)` overload whose first parameter `T` is a type --
  /// is a silent deduction failure that removes only that candidate from the
  /// overload set ([temp.arg]/2, [temp.deduct]/8), not a user-visible error.
  /// `typecheck_template_args` consults this to decide between throwing
  /// `template_arg_kind_mismatch_exceptiont` (caught by the candidate loop,
  /// which skips the candidate) and reporting a hard error.
  unsigned template_arg_candidate_matching = 0;

  /// RAII guard incrementing `template_arg_candidate_matching`.
  class template_arg_candidate_matchingt
  {
  public:
    explicit template_arg_candidate_matchingt(cpp_typecheckt &_cpp_typecheck)
      : cpp_typecheck(_cpp_typecheck)
    {
      ++cpp_typecheck.template_arg_candidate_matching;
    }
    ~template_arg_candidate_matchingt()
    {
      --cpp_typecheck.template_arg_candidate_matching;
    }

  private:
    cpp_typecheckt &cpp_typecheck;
  };

  /// Stack of currently-active target types for nested calls; pushed
  /// by `typecheck_side_effect_function_call(exprt &,
  /// const target_typet &)` and read by
  /// `typecheck_function_expr` when constructing `fargs`.  The
  /// resolver and conversion paths consult `fargs.target` to drive
  /// [temp.deduct.conv]/1 deduction.  See
  /// `doc/architectural/cpp-frontend-plan-target-type-threading.md`
  /// Phase 4.
  std::vector<target_typet> call_target_stack;
};

#endif // CPROVER_CPP_CPP_TYPECHECK_H
