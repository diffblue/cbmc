/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/byte_operators.h>
#include <util/range.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>

#include "boolbv.h"

/// Chains of nested let-expressions of at least this depth (measured along
/// where()) are converted iteratively (see convert_let). Shallower lets keep
/// using the straightforward recursive path.
static constexpr std::size_t LET_ITERATIVE_THRESHOLD = 16;

/// Iteratively alpha-rename, in place, every variable bound by a
/// let/quantifier/lambda/array-comprehension within \p root to a globally-fresh
/// identifier, respecting binding scopes and shadowing. Uses explicit work and
/// scope stacks, so it does not recurse and is safe on deeply nested input.
///
/// Renaming to fresh, unique names is what makes it sound to convert a let body
/// without the per-frame replace_symbolt of the recursive path: because every
/// bound name is unique, the conversions cached in bv_cache for sub-expressions
/// of a let body can never collide with other (free, or differently-bound)
/// occurrences of the original name.
///
/// Prototype limitation: occurrences of bound variables inside *types* (e.g. a
/// dependent array size) are not renamed. Such occurrences do not arise for
/// SMT-LIB let-bindings; the recursive path used for shallow lets continues to
/// handle them via replace_symbolt.
static void let_chain_alpha_rename(exprt &root, std::size_t &counter)
{
  struct taskt
  {
    enum kindt
    {
      VISIT,
      ENTER,
      LEAVE
    } kind;
    exprt *e;
    std::unordered_map<irep_idt, irep_idt> scope;
  };

  // scope stack: innermost scope last; maps original to fresh identifiers
  std::vector<std::unordered_map<irep_idt, irep_idt>> scopes;

  std::vector<taskt> stack;
  stack.push_back({taskt::VISIT, &root, {}});

  while(!stack.empty())
  {
    taskt task = std::move(stack.back());
    stack.pop_back();

    if(task.kind == taskt::ENTER)
    {
      scopes.push_back(std::move(task.scope));
      continue;
    }

    if(task.kind == taskt::LEAVE)
    {
      scopes.pop_back();
      continue;
    }

    exprt &e = *task.e;

    if(e.id() == ID_symbol)
    {
      const irep_idt &id = to_symbol_expr(e).get_identifier();
      for(auto scope = scopes.rbegin(); scope != scopes.rend(); ++scope)
      {
        auto found = scope->find(id);
        if(found != scope->end())
        {
          to_symbol_expr(e).set_identifier(found->second);
          break;
        }
      }
      continue;
    }

    const bool is_let = e.id() == ID_let;
    const bool is_binding = e.id() == ID_forall || e.id() == ID_exists ||
                            e.id() == ID_lambda ||
                            e.id() == ID_array_comprehension;

    if(is_let || is_binding)
    {
      auto &variables =
        is_let ? to_let_expr(e).variables() : to_binding_expr(e).variables();

      // generate fresh names and rewrite the variable declarations
      std::unordered_map<irep_idt, irep_idt> scope;
      ++counter;
      for(auto &variable : variables)
      {
        const irep_idt old_identifier = variable.get_identifier();
        const irep_idt new_identifier =
          "boolbvt::scope::" + std::to_string(counter) +
          "::" + id2string(old_identifier);
        scope.emplace(old_identifier, new_identifier);
        variable.set_identifier(new_identifier);
      }

      exprt &where =
        is_let ? to_let_expr(e).where() : to_binding_expr(e).where();

      // Schedule, to be executed in order: the let values in the *outer* scope
      // (concurrent binding: they do not see this frame's variables), then
      // enter this frame's scope, then the where-expression, then leave it.
      stack.push_back({taskt::LEAVE, nullptr, {}});
      stack.push_back({taskt::VISIT, &where, {}});
      stack.push_back({taskt::ENTER, nullptr, std::move(scope)});

      if(is_let)
      {
        auto &values = to_let_expr(e).values();
        for(auto value = values.rbegin(); value != values.rend(); ++value)
          stack.push_back({taskt::VISIT, &*value, {}});
      }

      continue;
    }

    for(auto operand = e.operands().rbegin(); operand != e.operands().rend();
        ++operand)
      stack.push_back({taskt::VISIT, &*operand, {}});
  }
}

bvt boolbvt::convert_let(const let_exprt &expr)
{
  // Probe the depth of the chain of nested let-expressions reachable through
  // where(); this is exactly the recursion depth the straightforward
  // implementation incurs. Shallow lets (the common case) keep using the
  // recursive implementation below, which also renames bound variables
  // occurring in types; only deep chains use the iterative path.
  std::size_t chain_depth = 0;
  for(const exprt *e = &expr.where();
      e->id() == ID_let && chain_depth < LET_ITERATIVE_THRESHOLD;
      e = &to_let_expr(*e).where())
  {
    ++chain_depth;
  }

  if(chain_depth >= LET_ITERATIVE_THRESHOLD)
    return convert_let_iterative(expr);

  const auto &variables = expr.variables();
  const auto &values = expr.values();

  DATA_INVARIANT(
    expr.type() == expr.where().type(),
    "let must have the type of the 'where' operand");

  // Check the types.
  for(auto &binding : make_range(variables).zip(values))
  {
    DATA_INVARIANT(
      binding.first.type() == binding.second.type(),
      "let value must have the type of the let symbol");
  }

  // A let expression can bind multiple symbols simultaneously.
  // This is a 'concurrent' binding, i.e., the symbols are not yet
  // visible when evaluating the values. SMT-LIB also has this
  // semantics. We therefore first convert all values,
  // and only then assign them.
  std::vector<bvt> converted_values;
  converted_values.reserve(variables.size());

  for(auto &value : values)
  {
    if(!bv_width.get_width_opt(value.type()).has_value())
      converted_values.emplace_back();
    else
      converted_values.push_back(convert_bv(value));
  }

  // get fresh bound symbols
  auto fresh_variables = fresh_binding(expr.binding());

  // Now assign
  for(const auto &binding : make_range(fresh_variables).zip(converted_values))
  {
    const auto &identifier = binding.first.identifier();

    // make the symbol visible
    if(binding.first.is_boolean())
    {
      DATA_INVARIANT(binding.second.size() == 1, "boolean values have one bit");
      symbols[identifier] = binding.second[0];
    }
    else
      map.set_literals(identifier, binding.first.type(), binding.second);
  }

  // for renaming the bound symbols
  replace_symbolt replace_symbol;

  for(const auto &pair : make_range(variables).zip(fresh_variables))
    replace_symbol.insert(pair.first, pair.second);

  // Connect fresh let-bound symbols to their values in the array theory.
  for(const auto &pair : make_range(fresh_variables).zip(values))
  {
    if(
      pair.first.type().id() == ID_array &&
      is_unbounded_array(to_array_type(pair.first.type())))
    {
      const exprt lowered_value = has_byte_operator(pair.second)
                                    ? lower_byte_operators(pair.second, ns)
                                    : pair.second;
      record_array_let_binding(pair.first, lowered_value);
    }
  }

  // rename the bound symbols in 'where'
  exprt where_renamed = expr.where();
  replace_symbol(where_renamed);

  // recursive call
  bvt result_bv = convert_bv(where_renamed);

  // the mapping can now be deleted
  for(const auto &entry : fresh_variables)
  {
    const auto &type = entry.type();
    if(type.id() == ID_bool)
      symbols.erase(entry.identifier());
    else
      map.erase_literals(entry.identifier(), type);
  }

  return result_bv;
}

bvt boolbvt::convert_let_iterative(const let_exprt &expr)
{
  // Alpha-rename all bound variables in the whole let-expression to
  // globally-fresh identifiers in a single iterative pass, then process the
  // chain of nested lets iteratively. Renaming up-front (rather than once per
  // frame, as the recursive path does) keeps bv_cache sound -- each bound name
  // is unique, so cached sub-expressions of a let body never collide with other
  // occurrences -- while avoiding both the per-frame O(depth) replace_symbolt
  // traversal (O(depth^2) overall) and the per-level recursion that overflows
  // the call stack on deep chains.
  exprt root = expr;
  let_chain_alpha_rename(root, scope_counter);

  // The bound variables of each frame, kept for tear-down in reverse order.
  std::vector<binding_exprt::variablest> frames;

  exprt *current = &root;
  while(current->id() == ID_let)
  {
    let_exprt &let_expr = to_let_expr(*current);
    const auto &variables = let_expr.variables();
    auto &values = let_expr.values();

    DATA_INVARIANT(
      let_expr.type() == let_expr.where().type(),
      "let must have the type of the 'where' operand");
    for(auto &binding : make_range(variables).zip(values))
    {
      DATA_INVARIANT(
        binding.first.type() == binding.second.type(),
        "let value must have the type of the let symbol");
    }

    // Convert all values first; concurrent binding means the values do not see
    // this frame's own variables (which have not been made visible yet).
    std::vector<bvt> converted_values;
    converted_values.reserve(variables.size());
    for(auto &value : values)
    {
      if(!bv_width.get_width_opt(value.type()).has_value())
        converted_values.emplace_back();
      else
        converted_values.push_back(convert_bv(value));
    }

    // Make this frame's (already fresh) variables visible.
    for(const auto &binding : make_range(variables).zip(converted_values))
    {
      const auto &identifier = binding.first.identifier();
      if(binding.first.is_boolean())
      {
        DATA_INVARIANT(
          binding.second.size() == 1, "boolean values have one bit");
        symbols[identifier] = binding.second[0];
      }
      else
        map.set_literals(identifier, binding.first.type(), binding.second);
    }

    // Connect fresh let-bound symbols to their values in the array theory.
    for(const auto &pair : make_range(variables).zip(values))
    {
      if(
        pair.first.type().id() == ID_array &&
        is_unbounded_array(to_array_type(pair.first.type())))
      {
        const exprt lowered_value = has_byte_operator(pair.second)
                                      ? lower_byte_operators(pair.second, ns)
                                      : pair.second;
        record_array_let_binding(pair.first, lowered_value);
      }
    }

    frames.push_back(variables);
    current = &let_expr.where();
  }

  // Convert the innermost where-expression once. Its bound-variable references
  // resolve through the symbols/map entries set up above.
  bvt result_bv = convert_bv(*current);

  // Tear down the frames in reverse order.
  for(auto frame = frames.rbegin(); frame != frames.rend(); ++frame)
  {
    for(const auto &entry : *frame)
    {
      const auto &type = entry.type();
      if(type.id() == ID_bool)
        symbols.erase(entry.identifier());
      else
        map.erase_literals(entry.identifier(), type);
    }
  }

  return result_bv;
}
