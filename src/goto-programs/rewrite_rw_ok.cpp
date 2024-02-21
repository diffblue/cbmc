/*******************************************************************\

Module: Rewrite {r,w,rw}_ok expressions as required by symbolic execution

Author: Michael Tautschnig

\*******************************************************************/

#include "rewrite_rw_ok.h"

#include <util/expr_iterator.h>
#include <util/pointer_expr.h>

#include <goto-programs/goto_model.h>

static std::optional<exprt> rewrite_rw_ok(exprt expr, const namespacet &ns)
{
  bool unchanged = true;

  for(auto it = expr.depth_begin(), itend = expr.depth_end();
      it != itend;) // no ++it
  {
    if(auto r_or_w_ok = expr_try_dynamic_cast<r_or_w_ok_exprt>(*it))
    {
      const auto &id = it->id();
      exprt replacement =
        prophecy_r_or_w_ok_exprt{
          id == ID_r_ok   ? ID_prophecy_r_ok
          : id == ID_w_ok ? ID_prophecy_w_ok
                          : ID_prophecy_rw_ok,
          r_or_w_ok->pointer(),
          r_or_w_ok->size(),
          ns.lookup(CPROVER_PREFIX "deallocated").symbol_expr(),
          ns.lookup(CPROVER_PREFIX "dead_object").symbol_expr()}
          .with_source_location(*it);

      it.mutate() = std::move(replacement);
      unchanged = false;
      it.next_sibling_or_parent();
    }
    else if(
      auto pointer_in_range =
        expr_try_dynamic_cast<pointer_in_range_exprt>(*it))
    {
      exprt replacement =
        prophecy_pointer_in_range_exprt{
          pointer_in_range->lower_bound(),
          pointer_in_range->pointer(),
          pointer_in_range->upper_bound(),
          ns.lookup(CPROVER_PREFIX "deallocated").symbol_expr(),
          ns.lookup(CPROVER_PREFIX "dead_object").symbol_expr()}
          .with_source_location(*it);

      it.mutate() = std::move(replacement);
      unchanged = false;
      it.next_sibling_or_parent();
    }
    else
      ++it;
  }

  if(unchanged)
    return {};
  else
    return std::move(expr);
}

static void rewrite_rw_ok(
  goto_functionst::goto_functiont &goto_function,
  const namespacet &ns)
{
  for(auto &instruction : goto_function.body.instructions)
    instruction.transform(
      [&ns](exprt expr) { return rewrite_rw_ok(expr, ns); });
}

void rewrite_rw_ok(goto_modelt &goto_model)
{
  const namespacet ns(goto_model.symbol_table);

  for(auto &gf_entry : goto_model.goto_functions.function_map)
    rewrite_rw_ok(gf_entry.second, ns);
}
