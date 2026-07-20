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

  void convert_initializer(symbolt &symbol);
  void convert_function(symbolt &symbol);

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

  std::string class_template_identifier(
    const irep_idt &base_name,
    const template_typet &template_type,
    const cpp_template_args_non_tct &partial_specialization_args);

  std::string function_template_identifier(
    const irep_idt &base_name,
    const template_typet &template_type,
    const typet &function_type);

  cpp_template_args_tct typecheck_template_args(
    const source_locationt &source_location,
    const symbolt &template_symbol,
    const cpp_template_args_non_tct &template_args);

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

  codet dtor(const symbolt &symb, const symbol_exprt &this_expr);

  void check_member_initializers(
    const struct_typet::basest &bases,
    const struct_typet::componentst &components,
    const irept &initializers,
    const irep_idt &class_identifier = irep_idt());

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

  void static_and_dynamic_initialization();
  void do_not_typechecked();
  void clean_up();
  void provide_stdlib_bodies();

  void add_base_components(
        const struct_typet &from,
        const irep_idt &access,
        struct_typet &to,
        std::set<irep_idt> &bases,
        std::set<irep_idt> &vbases,
        bool is_virtual);

  bool cast_away_constness(const typet &t1,
                           const typet &t2) const;

  void do_virtual_table(const symbolt &symbol);

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
  };

  typedef std::list<method_bodyt> method_bodiest;
  std::set<irep_idt> methods_seen;
  method_bodiest method_bodies;

  // Deferred method bodies for lazy template elaboration.
  std::map<irep_idt, method_bodyt> deferred_method_bodies;

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

  /// Static member symbols whose initializers are deferred until
  /// after the class body is fully declared.
  /// In-class initializers of static data members that could not be
  /// type-checked during member declaration and are re-attempted once the
  /// class is complete (N5008 [basic.scope.class]: earlier-declared member
  /// names, e.g. class-local typedefs, must be in scope for the
  /// initializer): (member symbol, enclosing class symbol) pairs.
  std::vector<std::pair<irep_idt, irep_idt>> deferred_static_initializers;

  /// Depth of typecheck_compound_body nesting, used to track
  /// recursive template elaboration.
  unsigned compound_body_depth = 0;
  bool suppress_elaborate = false;

  /// When true, typecheck_template_args does NOT expand pack-expansion
  /// template arguments ([temp.variadic]).  Set while matching a partial
  /// class-template specialization against actual arguments
  /// (disambiguate_template_classes), where the specialization's own
  /// parameter packs must be matched/deduced rather than substituted with an
  /// (unrelated) enclosing instantiation's pack.
  bool disable_template_arg_pack_expansion = false;

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
  void typecheck_enum_body(symbolt &symbol);
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
  void typecheck_block(code_blockt &) override;
  void typecheck_ifthenelse(code_ifthenelset &) override;
  void typecheck_while(code_whilet &) override;
  void typecheck_switch(codet &) override;

  const struct_typet &this_struct_type();

  std::optional<codet> cpp_destructor(
    const source_locationt &source_location,
    const exprt &object,
    bool force_direct = true);

  // expressions
  void explicit_typecast_ambiguity(exprt &);
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
  std::optional<typet> deduce_class_template_arguments(
    const cpp_namet &class_template_name,
    const std::vector<exprt> &args);
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

  void
  typecheck_function_call_arguments(side_effect_expr_function_callt &) override;

  void instantiate_generic_lambda(side_effect_expr_function_callt &);

  bool operator_is_overloaded(exprt &);
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
  std::optional<exprt> build_initializer_list_value(
    const struct_tag_typet &il_type,
    const exprt &init_list);

  void reference_initializer(exprt &expr, const reference_typet &type);

  void implicit_typecast(exprt &expr, const typet &type) override;

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

  void make_ptr_typecast(exprt &expr, const pointer_typet &dest_type);

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

  bool contains_cpp_name(const exprt &);

private:
  typedef std::list<irep_idt> dynamic_initializationst;
  dynamic_initializationst dynamic_initializations;
  bool disable_access_control;           // Disable protect and private
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
  std::unordered_set<irep_idt> deferred_typechecking;
  std::unordered_set<irep_idt> functions_being_typechecked;

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
