/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_TEMPLATE_MAP_H
#define CPROVER_CPP_TEMPLATE_MAP_H

#include <map>
#include <iosfwd>

#include <util/expr.h>

#include "cpp_template_args.h"

struct template_parametert;
class template_typet;

class template_mapt
{
public:
  // this maps template parameters to their instantiated value
  typedef std::map<irep_idt, typet> type_mapt;
  typedef std::map<irep_idt, exprt> expr_mapt;
  typedef std::map<irep_idt, std::size_t> pack_size_mapt;
  typedef std::map<irep_idt, std::vector<typet>> pack_args_mapt;
  type_mapt type_map;
  expr_mapt expr_map;
  pack_size_mapt pack_size_map;
  pack_args_mapt pack_args_map;

  void apply(exprt &dest) const;
  void apply(typet &dest) const;

  /// If \p param_type is a bare reference to a deduced template parameter
  /// pack (recorded in pack_args_map), return the deduced element types so a
  /// function parameter pack can be expanded ([temp.variadic]/5); else null.
  const std::vector<typet> *
  function_parameter_pack(const typet &param_type) const;

  /// Expand any function parameter pack in the parameter list of the
  /// function type \p function_type (ID_code or ID_function_type) into one
  /// parameter per deduced pack element ([temp.variadic]/5).  Unlike apply(),
  /// this performs only pack expansion and is used at the specific sites that
  /// reconstruct a function type from a variadic pattern (e.g. matching a
  /// `std::function<R(A...)>` partial specialization), so the general
  /// substitution path is unaffected.
  void expand_parameter_packs(typet &function_type) const;

  /// N5008 [temp.variadic]/5: expand pack expansions that appear as
  /// function-call arguments anywhere inside \p n (e.g. the `declval<A>()...`
  /// in `decltype(declval<F>()(declval<A>()...))`, the shape of
  /// libstdc++'s `__invoke_result` used to constrain
  /// `std::function<R(A...)>`'s converting constructor).  The parser marks
  /// such an argument with ID_ellipsis; each is replaced by one argument per
  /// deduced element of the referenced type parameter pack (substituting the
  /// element type for the pack reference), or by zero arguments for an empty
  /// pack.  Arguments that do not reference a deduced type pack are left
  /// untouched, so value parameter packs are unaffected.  Invoked from
  /// apply() so the expansion happens in every substitution/instantiation
  /// context, including nested trait instantiations.
  void expand_call_argument_packs(irept &n) const;

  void swap(template_mapt &template_map)
  {
    type_map.swap(template_map.type_map);
    expr_map.swap(template_map.expr_map);
    pack_size_map.swap(template_map.pack_size_map);
    pack_args_map.swap(template_map.pack_args_map);
  }

  exprt lookup(const irep_idt &identifier) const;
  typet lookup_type(const irep_idt &identifier) const;
  exprt lookup_expr(const irep_idt &identifier) const;

  /// Look up a template parameter by its base name suffix (after the last
  /// "::").  This handles the case where a template parameter was registered
  /// under a different scope prefix from the reference (e.g. a different
  /// instantiation scope-number for the same parameter -- see Violation V1 in
  /// doc/architectural/cpp-frontend-review-2026-06-24-template-map-scope.md).
  ///
  /// When several live bindings share the short name (an ambiguity that, per
  /// N5008 [basic.scope.temp]/2, must be resolved to the nearest enclosing
  /// scope rather than arbitrarily), \p reference_id -- the full
  /// scope-qualified identifier of the reference being resolved -- is used to
  /// prefer the candidate that shares the longest leading scope path with the
  /// reference.  This is a step toward exact scope-identity resolution; do not
  /// add new callers without passing the reference id.
  exprt lookup_by_suffix(
    const std::string &suffix,
    const irep_idt &reference_id = irep_idt()) const;

  void print(std::ostream &out) const;

  void clear()
  {
    type_map.clear();
    expr_map.clear();
    pack_size_map.clear();
    pack_args_map.clear();
  }

  void set(
    const template_parametert &parameter,
    const exprt &value);

  void build(
    const template_typet &template_type,
    const cpp_template_args_tct &template_args);

  void build_unassigned(
    const template_typet &template_type);

  cpp_template_args_tct build_template_args(
    const template_typet &template_type) const;
};

class cpp_saved_template_mapt
{
public:
  // CONFORMANCE NOTE (Violation V2, see doc/architectural/
  // cpp-frontend-review-2026-06-24-template-map-scope.md): this saves and
  // restores the WHOLE flat template_map by copy, so while an inner
  // instantiation runs the outer instantiation's parameter bindings remain
  // present in the same maps.  Combined with the short-name resolution
  // (Violation V1) this lets one instantiation reach another's bindings,
  // contrary to N5008 [temp.point]/1 (each specialization is instantiated in a
  // definite context, not the union of all live bindings).  The scoped
  // structural change replaces this with a per-instantiation frame stack.
  explicit cpp_saved_template_mapt(template_mapt &map):
    old_map(map), map(map)
  {
  }

  ~cpp_saved_template_mapt()
  {
    #if 0
    std::cout << "RESTORING TEMPLATE MAP\n";
    #endif
    map.swap(old_map);
  }

private:
  template_mapt old_map;
  template_mapt &map;
};

#endif // CPROVER_CPP_TEMPLATE_MAP_H
