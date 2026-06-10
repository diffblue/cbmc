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
  /// "::"). This handles the case where a template parameter was registered
  /// under a different scope prefix (e.g., forward declaration vs definition).
  exprt lookup_by_suffix(const std::string &suffix) const;

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
