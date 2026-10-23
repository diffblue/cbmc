/*******************************************************************\

Module: Lift nested dereferences into temporaries

Author: Kiro

\*******************************************************************/

/// \file
/// Lift nested (chained) dereferences into temporaries.

#include "lift_nested_dereferences.h"

#include <util/expr_util.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>

#include <analyses/dirty.h>

#include "goto_model.h"

/// Collect, into \p candidates, every expression that occurs as the pointer
/// operand of a dereference and itself contains a dereference (i.e. the
/// intermediate pointer of a chained dereference such as `a->b` in
/// `a->b->c`). These are the expressions we hoist into temporaries.
static void collect_candidates(
  const exprt &expr,
  std::unordered_set<exprt, irep_hash> &candidates)
{
  if(expr.id() == ID_dereference)
  {
    const exprt &pointer = to_dereference_expr(expr).pointer();
    if(has_subexpr(pointer, ID_dereference))
      candidates.insert(pointer);
  }

  for(const auto &op : expr.operands())
    collect_candidates(op, candidates);
}

/// True if \p expr reads the symbol with the given \p identifier.
static bool mentions_symbol(const exprt &expr, const irep_idt &identifier)
{
  return has_subexpr(
    expr,
    [&identifier](const exprt &sub)
    {
      return sub.id() == ID_symbol &&
             to_symbol_expr(sub).get_identifier() == identifier;
    });
}

namespace
{
class lift_nested_dereferencest
{
public:
  lift_nested_dereferencest(
    goto_programt &body,
    symbol_table_baset &symbol_table,
    const irep_idt &mode,
    const dirtyt &dirty)
    : body(body), symbol_table(symbol_table), mode(mode), dirty(dirty)
  {
  }

  void operator()();

private:
  goto_programt &body;
  symbol_table_baset &symbol_table;
  const irep_idt &mode;
  const dirtyt &dirty;

  std::unordered_set<exprt, irep_hash> candidates;
  // Candidate expression -> temporary currently holding its value.
  std::unordered_map<exprt, symbol_exprt, irep_hash> available;

  exprt substitute(const exprt &expr, goto_programt &prefix, bool lvalue);
  symbol_exprt get_temporary(const exprt &candidate, goto_programt &prefix);
  void invalidate(const goto_programt::instructiont &instruction);
};

/// Replace each candidate intermediate-pointer subexpression of \p expr that is
/// *read* by a temporary holding its value, emitting any required
/// declarations/assignments into \p prefix. \p lvalue indicates whether \p expr
/// occurs in an lvalue position (an assignment target, or the operand of
/// address-of). A candidate is only substituted in rvalue (read) positions:
/// substituting it in an lvalue position would redirect the write to the
/// temporary, and substituting the operand of address-of would take the address
/// of the temporary rather than of the original object. Keeping those intact
/// preserves program semantics and avoids corrupting contract instrumentation
/// that snapshots the addresses and extents of assignable targets.
exprt lift_nested_dereferencest::substitute(
  const exprt &expr,
  goto_programt &prefix,
  bool lvalue)
{
  if(!lvalue && candidates.count(expr) != 0)
    return get_temporary(expr, prefix);

  exprt result = expr;

  // Propagate the lvalue/rvalue context structurally into sub-expressions.
  if(result.id() == ID_address_of)
  {
    // The operand is the object whose address is taken: an lvalue.
    auto &address_of = to_address_of_expr(result);
    address_of.object() = substitute(address_of.object(), prefix, true);
    return result;
  }
  if(result.id() == ID_dereference)
  {
    // `*p` reads the pointer `p`; the pointer operand is always an rvalue.
    auto &dereference = to_dereference_expr(result);
    dereference.pointer() = substitute(dereference.pointer(), prefix, false);
    return result;
  }
  if(result.id() == ID_member)
  {
    // A member of an lvalue is an lvalue; a member of an rvalue is an rvalue.
    auto &member = to_member_expr(result);
    member.compound() = substitute(member.compound(), prefix, lvalue);
    return result;
  }
  if(result.id() == ID_index)
  {
    // `a[i]` inherits the lvalue-ness of the array; the index is read.
    auto &index = to_index_expr(result);
    index.array() = substitute(index.array(), prefix, lvalue);
    index.index() = substitute(index.index(), prefix, false);
    return result;
  }

  // Any other expression is an rvalue, and so are all of its operands.
  for(auto &op : result.operands())
    op = substitute(op, prefix, false);
  return result;
}

/// Return the temporary holding \p candidate, creating and assigning it (in
/// \p prefix) if it is not already available.
symbol_exprt lift_nested_dereferencest::get_temporary(
  const exprt &candidate,
  goto_programt &prefix)
{
  auto found = available.find(candidate);
  if(found != available.end())
    return found->second;

  // Substitute any nested candidates within the value being assigned, so that
  // deeper chains are flattened and share temporaries too. The value is read,
  // so this is an rvalue context.
  exprt value = candidate;
  for(auto &op : value.operands())
    op = substitute(op, prefix, false);

  const symbol_exprt tmp = get_fresh_aux_symbol(
                             candidate.type(),
                             "symex",
                             "deref_tmp",
                             candidate.source_location(),
                             mode,
                             symbol_table)
                             .symbol_expr();

  prefix.add(goto_programt::make_decl(tmp, candidate.source_location()));
  prefix.add(
    goto_programt::make_assignment(tmp, value, candidate.source_location()));

  available.emplace(candidate, tmp);
  return tmp;
}

/// Drop availability entries whose value might have changed because of
/// \p instruction.
void lift_nested_dereferencest::invalidate(
  const goto_programt::instructiont &instruction)
{
  const auto invalidate_all = [this]() { available.clear(); };

  const auto invalidate_symbol = [this](const irep_idt &identifier)
  {
    for(auto it = available.begin(); it != available.end();)
    {
      if(mentions_symbol(it->first, identifier))
        it = available.erase(it);
      else
        ++it;
    }
  };

  switch(instruction.type())
  {
  case ASSIGN:
  {
    const exprt &lhs = instruction.assign_lhs();
    if(lhs.id() == ID_symbol && !dirty(to_symbol_expr(lhs)))
    {
      // A write to a non-address-taken variable can only change that
      // variable, so only entries reading it become stale.
      invalidate_symbol(to_symbol_expr(lhs).get_identifier());
    }
    else
    {
      // A write through a pointer (or to an address-taken variable) might
      // alias anything a candidate reads.
      invalidate_all();
    }
    break;
  }
  case FUNCTION_CALL:
    // The callee may modify globals or memory reachable through pointers.
    invalidate_all();
    break;
  case DECL:
    invalidate_symbol(instruction.decl_symbol().get_identifier());
    break;
  case DEAD:
    invalidate_symbol(instruction.dead_symbol().get_identifier());
    break;
  case CATCH:
  case THROW:
  case OTHER:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
    invalidate_all();
    break;
  case GOTO:
  case ASSUME:
  case ASSERT:
  case SKIP:
  case SET_RETURN_VALUE:
  case START_THREAD:
  case END_THREAD:
  case END_FUNCTION:
  case LOCATION:
  case INCOMPLETE_GOTO:
  case NO_INSTRUCTION_TYPE:
    // No memory is modified by these in a way that affects candidate values.
    break;
  }
}

void lift_nested_dereferencest::operator()()
{
  for(const auto &instruction : body.instructions)
    instruction.apply([this](const exprt &e)
                      { collect_candidates(e, candidates); });

  if(candidates.empty())
    return;

  for(auto it = body.instructions.begin(); it != body.instructions.end(); ++it)
  {
    goto_programt prefix;

    if(it->is_assign())
    {
      // The left-hand side is an lvalue (write target); the right-hand side is
      // read.
      it->assign_lhs_nonconst() = substitute(it->assign_lhs(), prefix, true);
      it->assign_rhs_nonconst() = substitute(it->assign_rhs(), prefix, false);
    }
    else if(it->is_function_call())
    {
      // The return-value target (if any) is an lvalue; the called function and
      // the arguments are read.
      if(it->call_lhs().is_not_nil())
        it->call_lhs() = substitute(it->call_lhs(), prefix, true);
      it->call_function() = substitute(it->call_function(), prefix, false);
      for(auto &argument : it->call_arguments())
        argument = substitute(argument, prefix, false);
    }
    else
    {
      // No other instruction has an lvalue operand; treat everything as read.
      // (address-of operands are still handled as lvalues inside substitute.)
      it->transform(
        [&](exprt e) -> std::optional<exprt>
        {
          exprt rewritten = substitute(e, prefix, false);
          if(rewritten == e)
            return {};
          return rewritten;
        });
    }

    // The (now rewritten) instruction may invalidate available temporaries.
    invalidate(*it);

    const std::size_t inserted = prefix.instructions.size();
    if(inserted != 0)
    {
      // insert_before_swap preserves jumps targeting `it`.
      body.insert_before_swap(it, prefix);
      // Advance past the inserted declarations/assignments to the (rewritten)
      // original instruction.
      std::advance(it, inserted);
    }
  }
}
} // namespace

void lift_nested_dereferences(
  goto_functiont &goto_function,
  symbol_table_baset &symbol_table,
  const irep_idt &mode)
{
  if(!goto_function.body_available())
    return;

  const dirtyt dirty(goto_function);
  lift_nested_dereferencest{goto_function.body, symbol_table, mode, dirty}();
}

void lift_nested_dereferences(goto_modelt &goto_model)
{
  // The transformation reads each chained intermediate pointer once and reuses
  // the result. In a concurrent program the dereferenced memory may be shared,
  // and collapsing two reads of a shared location into one removes thread
  // interleavings (the two reads could observe different values), which could
  // hide genuine data-race-dependent bugs. We therefore conservatively skip the
  // whole transformation for concurrent programs. (For thread-local data it
  // would be sound, but distinguishing that requires a points-to/escape
  // analysis that is out of scope here.)
  for(const auto &entry : goto_model.goto_functions.function_map)
  {
    for(const auto &instruction : entry.second.body.instructions)
    {
      if(instruction.is_start_thread())
        return;
    }
  }

  for(auto &entry : goto_model.goto_functions.function_map)
  {
    const symbolt &function_symbol =
      goto_model.symbol_table.lookup_ref(entry.first);
    lift_nested_dereferences(
      entry.second, goto_model.symbol_table, function_symbol.mode);
  }

  goto_model.goto_functions.update();
}
