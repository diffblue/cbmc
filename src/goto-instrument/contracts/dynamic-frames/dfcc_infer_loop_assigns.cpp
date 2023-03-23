/*******************************************************************\

Module: Dynamic frame condition checking

Author: Remi Delmas, delmasrd@amazon.com

\*******************************************************************/
#include "dfcc_infer_loop_assigns.h"

#include <util/expr.h>
#include <util/find_symbols.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>

#include <goto-instrument/havoc_utils.h>

#include "dfcc_root_object.h"

/// Builds a call expression `object_whole(expr)`
static exprt
make_object_whole_call_expr(const exprt &expr, const namespacet &ns)
{
  const symbolt &object_whole_sym = ns.lookup(CPROVER_PREFIX "object_whole");
  const code_typet &object_whole_code_type =
    to_code_type(object_whole_sym.type);
  return side_effect_expr_function_callt(
    object_whole_sym.symbol_expr(),
    {{expr}},
    object_whole_code_type.return_type(),
    expr.source_location());
}

/// Returns true iff \p expr contains at least one identifier found in
/// \p identifiers.
static bool
depends_on(const exprt &expr, std::unordered_set<irep_idt> identifiers)
{
  const std::unordered_set<irep_idt> ids = find_symbol_identifiers(expr);
  for(const auto &id : ids)
  {
    if(identifiers.find(id) != identifiers.end())
      return true;
  }
  return false;
}

assignst dfcc_infer_loop_assigns(
  const local_may_aliast &local_may_alias,
  const loopt &loop_instructions,
  const source_locationt &loop_head_location,
  const namespacet &ns)
{
  // infer
  assignst assigns;
  get_assigns(local_may_alias, loop_instructions, assigns);

  // compute locals
  std::unordered_set<irep_idt> loop_locals;
  for(const auto &target : loop_instructions)
  {
    if(target->is_decl())
      loop_locals.insert(target->decl_symbol().get_identifier());
  }

  // widen or drop targets that depend on loop-locals or are non-constant,
  // ie. depend on other locations assigned by the loop.
  // e.g: if the loop assigns {i, a[i]}, then a[i] is non-constant.
  havoc_utils_is_constantt is_constant(assigns, ns);
  assignst result;
  for(const auto &expr : assigns)
  {
    if(depends_on(expr, loop_locals))
    {
      // Target depends on loop locals, attempt widening to the root object
      auto root_objects = dfcc_root_objects(expr);
      for(const auto &root_object : root_objects)
      {
        if(!depends_on(root_object, loop_locals))
        {
          address_of_exprt address_of_root_object(root_object);
          address_of_root_object.add_source_location() =
            root_object.source_location();
          result.emplace(
            make_object_whole_call_expr(address_of_root_object, ns));
        }
      }
    }
    else
    {
      address_of_exprt address_of_expr(expr);
      address_of_expr.add_source_location() = expr.source_location();
      if(!is_constant(address_of_expr))
      {
        // Target address is not constant, widening to the whole object
        result.emplace(make_object_whole_call_expr(address_of_expr, ns));
      }
      else
      {
        result.emplace(expr);
      }
    }
  }

  return result;
}
