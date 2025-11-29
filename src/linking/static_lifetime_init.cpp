/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "static_lifetime_init.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/expr_initializer.h>
#include <util/find_symbols.h>
#include <util/invariant.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include <goto-programs/goto_model.h>

#include <ansi-c/goto-conversion/goto_convert_functions.h>

#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

using dependency_mapt =
  std::unordered_map<irep_idt, std::unordered_set<irep_idt>>;

/// Build a dependency graph for static lifetime objects.
/// Returns a map from symbol identifier to the set of identifiers it depends
/// on.  According to C standard (C99/C11 Section 6.7.9 and 6.6 paragraph 9):
/// - Objects with static storage duration can be initialized with constant
///   expressions or string literals
/// - An address constant is a pointer to an lvalue designating an object of
///   static storage duration
/// - When a static object's initializer references another static object,
///   that referenced object must be initialized first to maintain proper
///   initialization order
static dependency_mapt build_static_initialization_dependencies(
  const std::set<std::string> &symbols,
  const namespacet &ns)
{
  dependency_mapt dependencies;

  for(const std::string &id : symbols)
  {
    const symbolt &symbol = ns.lookup(id);

    // Only track dependencies for objects with static lifetime that have
    // initializers
    if(
      !symbol.is_static_lifetime || symbol.is_type || symbol.is_macro ||
      symbol.type.id() == ID_code || symbol.type.id() == ID_empty)
    {
      continue;
    }

    // Skip if no initializer or nondet initializer (either as a direct
    // ID_nondet or as a side_effect nondet expression)
    if(
      symbol.value.is_nil() || symbol.value.id() == ID_nondet ||
      (symbol.value.id() == ID_side_effect &&
       to_side_effect_expr(symbol.value).get_statement() == ID_nondet))
    {
      continue;
    }

    // Find all symbols referenced in the initializer.  Note that
    // find_symbol_identifiers also reports identifiers referenced from types
    // nested in the initializer (e.g. a size symbol in an array type), not
    // just value sub-expressions.  This only ever over-approximates the
    // dependency set, which is safe (harmless) for initialization ordering.
    find_symbols_sett referenced_symbols =
      find_symbol_identifiers(symbol.value);

    // Add dependencies on other static lifetime objects
    for(const irep_idt &ref_id : referenced_symbols)
    {
      // Skip self-references
      if(ref_id == symbol.name)
        continue;

      // Check if the referenced symbol is in our set of symbols to initialize
      if(symbols.find(id2string(ref_id)) == symbols.end())
        continue;

      // Verify it's a static lifetime object
      if(ns.lookup(ref_id).is_static_lifetime)
        dependencies[symbol.name].insert(ref_id);
    }
  }

  return dependencies;
}

/// Depth-first post-order visit of \p id and the static objects its
/// initializer depends on, appending each symbol to \p result only after all
/// of its dependencies.  Dependencies are visited in alphabetical order for
/// reproducibility.  Cycles -- which can occur with mutually-referential
/// address constants (e.g. two globals taking each other's addresses), valid
/// C -- are broken by ignoring the back-edge: a node already \p in_progress is
/// skipped, so the original visit for that node completes and emits it exactly
/// once.
/// \param id: symbol to visit
/// \param symbols: the set of symbols being ordered (dependencies outside this
///   set are ignored)
/// \param dependencies: initialization dependency graph
/// \param [in,out] visited: symbols already emitted to \p result
/// \param [in,out] in_progress: symbols on the current DFS path (cycle
///   detection)
/// \param [in,out] result: initialization order being built
static void topological_sort_visit(
  const irep_idt &id,
  const std::set<std::string> &symbols,
  const dependency_mapt &dependencies,
  std::unordered_set<irep_idt> &visited,
  std::unordered_set<irep_idt> &in_progress,
  std::vector<irep_idt> &result)
{
  // If already visited, nothing to do
  if(visited.find(id) != visited.end())
    return;

  // Break cycles by ignoring the back-edge (see function documentation).
  if(!in_progress.insert(id).second)
    return;

  // Visit all dependencies first
  auto dep_it = dependencies.find(id);
  if(dep_it != dependencies.end())
  {
    // Sort dependencies alphabetically for reproducibility
    std::set<std::string> sorted_deps;
    for(const irep_idt &dep : dep_it->second)
      sorted_deps.insert(id2string(dep));

    for(const std::string &dep : sorted_deps)
    {
      // Only visit if it's in our symbol set
      if(symbols.find(dep) != symbols.end())
        topological_sort_visit(
          dep, symbols, dependencies, visited, in_progress, result);
    }
  }

  in_progress.erase(id);
  visited.insert(id);
  result.push_back(id);
}

/// Perform a topological sort on symbols considering their initialization
/// dependencies. Returns a vector of symbol identifiers in initialization
/// order. Uses alphabetical ordering as a tiebreaker for reproducibility.
static std::vector<irep_idt> topological_sort_with_dependencies(
  const std::set<std::string> &symbols,
  const dependency_mapt &dependencies)
{
  std::vector<irep_idt> result;
  std::unordered_set<irep_idt> visited;
  std::unordered_set<irep_idt> in_progress; // For cycle detection

  // Process all symbols in alphabetical order for reproducibility
  for(const std::string &id : symbols)
    topological_sort_visit(
      id, symbols, dependencies, visited, in_progress, result);

  return result;
}

static std::optional<codet> static_lifetime_init(
  const irep_idt &identifier,
  symbol_table_baset &symbol_table)
{
  const namespacet ns(symbol_table);
  const symbolt &symbol = ns.lookup(identifier);

  if(!symbol.is_static_lifetime)
    return {};

  if(symbol.is_type || symbol.is_macro)
    return {};

  // special values
  if(
    identifier == CPROVER_PREFIX "constant_infinity_uint" ||
    identifier == CPROVER_PREFIX "memory" || identifier == "__func__" ||
    identifier == "__FUNCTION__" || identifier == "__PRETTY_FUNCTION__" ||
    identifier == "argc'" || identifier == "argv'" || identifier == "envp'" ||
    identifier == "envp_size'")
    return {};

  // just for linking
  if(identifier.starts_with(CPROVER_PREFIX "architecture_"))
    return {};

  // check type
  if(symbol.type.id() == ID_code || symbol.type.id() == ID_empty)
    return {};

  if(symbol.type.id() == ID_array && to_array_type(symbol.type).size().is_nil())
  {
    if(symbol.is_extern)
      return {};
    // The C front-end adjusts non-extern tentative array definitions to size 1
    // during typecheck (C standard 6.9.2, paragraph 5), keeping the symbol's
    // type and its uses in code consistent. As a safety net for symbols
    // produced by other means (other front-ends, instrumentation, or
    // pre-existing goto binaries) that did not undergo that adjustment, patch
    // the size in place here rather than aborting.
    symbol_table.get_writeable_ref(identifier)
      .type.set(ID_size, from_integer(1, size_type()));
  }

  if(
    (symbol.type.id() == ID_struct_tag &&
     ns.follow_tag(to_struct_tag_type(symbol.type)).is_incomplete()) ||
    (symbol.type.id() == ID_union_tag &&
     ns.follow_tag(to_union_tag_type(symbol.type)).is_incomplete()))
  {
    return {}; // do not initialize
  }

  exprt rhs;

  if((symbol.value.is_nil() && symbol.is_extern) ||
     symbol.value.id() == ID_nondet)
  {
    if(symbol.value.get_bool(ID_C_no_nondet_initialization))
      return {};

    // Nondet initialise if not linked, or if explicitly requested.
    // Compilers would usually complain about the unlinked symbol case.
    const auto nondet = nondet_initializer(symbol.type, symbol.location, ns);
    CHECK_RETURN(nondet.has_value());
    rhs = *nondet;
  }
  else if(symbol.value.is_nil())
  {
    const auto zero = zero_initializer(symbol.type, symbol.location, ns);
    CHECK_RETURN(zero.has_value());
    rhs = *zero;
  }
  else
    rhs = symbol.value;

  return code_frontend_assignt{symbol.symbol_expr(), rhs, symbol.location};
}

void static_lifetime_init(
  symbol_table_baset &symbol_table,
  const source_locationt &source_location)
{
  PRECONDITION(symbol_table.has_symbol(INITIALIZE_FUNCTION));

  const namespacet ns(symbol_table);

  symbolt &init_symbol = symbol_table.get_writeable_ref(INITIALIZE_FUNCTION);

  init_symbol.value=code_blockt();
  init_symbol.value.add_source_location()=source_location;

  code_blockt &dest=to_code_block(to_code(init_symbol.value));

  // add the magic label to hide
  dest.add(code_labelt(CPROVER_PREFIX "HIDE", code_skipt()));

  // do assignments based on "value"

  // Build dependency graph for static lifetime initialization.
  // According to the C standard (C99/C11):
  // - Section 6.7.9 paragraph 4: All expressions in an initializer for an
  //   object that has static storage duration shall be constant expressions
  //   or string literals.
  // - Section 6.6 paragraph 9: An address constant is a null pointer, a pointer
  //   to an lvalue designating an object of static storage duration, or a
  //   pointer to a function designator.
  // - Section 6.2.4: Objects with static storage duration are initialized
  //   before program startup.
  //
  // When one static object's initializer takes the address of another static
  // object, the referenced object must be initialized first to ensure the
  // address constant is properly available.

  // First, collect all symbols and sort alphabetically for reproducible results
  std::set<std::string> symbols;

  for(const auto &symbol_pair : symbol_table.symbols)
  {
    symbols.insert(id2string(symbol_pair.first));
  }

  // Build dependency graph
  auto dependencies = build_static_initialization_dependencies(symbols, ns);

  // Separate CPROVER framework variables from user variables.
  // Sorting each group independently is safe: CPROVER symbols are always
  // initialized first, and cross-group dependencies (user -> CPROVER) are
  // satisfied by that ordering.  Dependencies in the other direction
  // (CPROVER -> user) do not occur; this is asserted below so that a future
  // violation fails loudly rather than silently producing a wrong order.
  std::set<std::string> cprover_symbols;
  std::set<std::string> user_symbols;

  for(const std::string &id : symbols)
  {
    if(has_prefix(id, CPROVER_PREFIX))
      cprover_symbols.insert(id);
    else
      user_symbols.insert(id);
  }

  // A CPROVER symbol must not depend on a user symbol: each group is sorted in
  // isolation, so such a cross-group edge would be dropped and mis-order the
  // initialization.
  for(const std::string &id : cprover_symbols)
  {
    auto dep_it = dependencies.find(id);
    if(dep_it != dependencies.end())
    {
      for(const irep_idt &dep : dep_it->second)
      {
        DATA_INVARIANT(
          cprover_symbols.find(id2string(dep)) != cprover_symbols.end(),
          "CPROVER static initializer must not depend on a user symbol");
      }
    }
  }

  // Initialize framework variables first, then all other variables; within
  // each group, order by initialization dependencies.
  const auto emit_in_dependency_order = [&](const std::set<std::string> &group)
  {
    for(const irep_idt &id :
        topological_sort_with_dependencies(group, dependencies))
    {
      auto code = static_lifetime_init(id, symbol_table);
      if(code.has_value())
        dest.add(std::move(*code));
    }
  };

  emit_in_dependency_order(cprover_symbols);
  emit_in_dependency_order(user_symbols);

  // now call designated "initialization" functions

  for(const std::string &id : symbols)
  {
    const symbolt &symbol=ns.lookup(id);

    if(symbol.type.id() != ID_code)
      continue;

    const code_typet &code_type = to_code_type(symbol.type);
    if(
      code_type.return_type().id() == ID_constructor &&
      code_type.parameters().empty())
    {
      dest.add(code_expressiont{side_effect_expr_function_callt{
        symbol.symbol_expr(), {}, code_type.return_type(), source_location}});
    }
  }
}

void recreate_initialize_function(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  auto unloaded = goto_model.unload(INITIALIZE_FUNCTION);
  PRECONDITION(unloaded == 1);

  static_lifetime_init(
    goto_model.symbol_table,
    goto_model.symbol_table.lookup_ref(INITIALIZE_FUNCTION).location);
  goto_convert(
    INITIALIZE_FUNCTION,
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);
  goto_model.goto_functions.update();
}
