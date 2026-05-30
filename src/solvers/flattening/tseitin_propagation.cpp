/// \file
/// Tseitin-aware boolean propagation for the algebraic solver.
/// See `tseitin_propagation.h` for motivation and soundness.

#include "tseitin_propagation.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/expr_util.h>
#include <util/std_expr.h>

#include <algorithm>
#include <unordered_set>

bool tseitin_propagatort::is_bool_typed(const typet &t)
{
  if(t.id() == ID_bool)
    return true;
  if(auto bv = type_try_dynamic_cast<bitvector_typet>(t))
    return bv->get_width() == 1;
  return false;
}

std::optional<mp_integer> tseitin_propagatort::as_const(const exprt &e)
{
  if(e.is_constant())
  {
    if(e.is_true())
      return mp_integer{1};
    if(e.is_false())
      return mp_integer{0};
    if(auto v = numeric_cast<mp_integer>(to_constant_expr(e)))
      return *v;
  }
  return std::nullopt;
}

/// If \p e is semantically equivalent to "sym" or "not sym" (where
/// sym is a 1-bit / boolean symbol), return the symbol identifier
/// and a polarity bit. Recognises:
/// \code
///   sym                       → (sym, 1)
///   (equal sym 1)             → (sym, 1)
///   (equal sym 0)             → (sym, 0)
///   (equal 1 sym)             → (sym, 1)
///   (equal 0 sym)             → (sym, 0)
///   (not E)                   → flipped(E)
///   (bitnot E) (1-bit / bool) → flipped(E)
///   (notequal sym const)      → flipped of (equal sym const)
/// \endcode
/// where flipped(...) recurses with polarity inverted.
static std::optional<std::pair<irep_idt, int>> extract_bool_atom(const exprt &e)
{
  if(e.id() == ID_symbol)
  {
    if(tseitin_propagatort::is_bool_typed_static(e.type()))
      return std::pair{to_symbol_expr(e).get_identifier(), 1};
  }
  if(e.id() == ID_equal && e.operands().size() == 2)
  {
    const auto &lhs = e.operands()[0];
    const auto &rhs = e.operands()[1];
    auto try_match = [](const exprt &sym, const exprt &c)
      -> std::optional<std::pair<irep_idt, int>>
    {
      if(
        sym.id() == ID_symbol &&
        tseitin_propagatort::is_bool_typed_static(sym.type()))
      {
        if(c.is_constant())
        {
          if(c.is_true())
            return std::pair{to_symbol_expr(sym).get_identifier(), 1};
          if(c.is_false())
            return std::pair{to_symbol_expr(sym).get_identifier(), 0};
          if(auto v = numeric_cast<mp_integer>(to_constant_expr(c)))
            return std::pair{
              to_symbol_expr(sym).get_identifier(), *v == 1 ? 1 : 0};
        }
      }
      return std::nullopt;
    };
    if(auto m = try_match(lhs, rhs))
      return m;
    if(auto m = try_match(rhs, lhs))
      return m;
  }
  if((e.id() == ID_not || e.id() == ID_bitnot) && e.operands().size() == 1)
  {
    if(auto inner = extract_bool_atom(e.operands()[0]))
      return std::pair{inner->first, 1 - inner->second};
  }
  if(e.id() == ID_notequal && e.operands().size() == 2)
  {
    auto eq = equal_exprt(e.operands()[0], e.operands()[1]);
    if(auto inner = extract_bool_atom(eq))
      return std::pair{inner->first, 1 - inner->second};
  }
  return std::nullopt;
}

void tseitin_propagatort::ingest(const equal_exprt &eq)
{
  const exprt &lhs = eq.lhs();
  const exprt &rhs = eq.rhs();

  // Try canonicalising each side to a bool atom (sym, polarity).
  auto lhs_atom = extract_bool_atom(lhs);
  auto rhs_atom = extract_bool_atom(rhs);

  // Pattern: (= bool_atom constant)  →  set known value of the
  // underlying symbol (with polarity adjustment).
  if(lhs_atom)
  {
    if(auto v = as_const(rhs))
    {
      mp_integer actual = lhs_atom->second == 1 ? *v : (mp_integer{1} - *v);
      auto it = known.find(lhs_atom->first);
      if(it != known.end() && it->second != actual)
        contradiction = true;
      else
        known[lhs_atom->first] = actual;
      return;
    }
  }
  if(rhs_atom)
  {
    if(auto v = as_const(lhs))
    {
      mp_integer actual = rhs_atom->second == 1 ? *v : (mp_integer{1} - *v);
      auto it = known.find(rhs_atom->first);
      if(it != known.end() && it->second != actual)
        contradiction = true;
      else
        known[rhs_atom->first] = actual;
      return;
    }
  }

  // Pattern: (= bool_atom non_constant_expr)  →  store a definition.
  // For polarity 1, defs[sym] = rhs. For polarity 0, defs[sym]
  // would be ¬rhs, which we represent as a not_exprt wrapper.
  // The forward `evaluate` and backward `enforce` already understand
  // ID_not / ID_bitnot wrappers.
  auto store_def = [&](const irep_idt &sym, int polarity, const exprt &val)
  {
    if(defs.find(sym) != defs.end())
      return;
    if(polarity == 1)
      defs[sym] = val;
    else
      defs[sym] = not_exprt{val};
  };

  if(lhs_atom && !rhs.is_constant())
  {
    store_def(lhs_atom->first, lhs_atom->second, rhs);
    return;
  }
  if(rhs_atom && !lhs.is_constant())
  {
    store_def(rhs_atom->first, rhs_atom->second, lhs);
    return;
  }
}

std::optional<mp_integer> tseitin_propagatort::evaluate(const exprt &e)
{
  if(auto v = as_const(e))
    return v;
  if(e.id() == ID_symbol && is_bool_typed(e.type()))
  {
    const auto &id = to_symbol_expr(e).get_identifier();
    auto it = known.find(id);
    if(it != known.end())
      return it->second;
    auto def_it = defs.find(id);
    if(def_it != defs.end())
    {
      auto v = evaluate(def_it->second);
      if(v.has_value())
        known[id] = *v;
      return v;
    }
    return std::nullopt;
  }
  if(e.id() == ID_bitnot || e.id() == ID_not)
  {
    if(e.operands().size() != 1)
      return std::nullopt;
    auto v = evaluate(e.operands()[0]);
    if(!v.has_value())
      return std::nullopt;
    return mp_integer{1} - *v;
  }
  if(e.id() == ID_bitor || e.id() == ID_or)
  {
    bool any_unknown = false;
    for(const auto &op : e.operands())
    {
      auto v = evaluate(op);
      if(!v.has_value())
        any_unknown = true;
      else if(*v != 0)
        return mp_integer{1}; // OR with a 1 is 1 regardless of unknowns
    }
    if(any_unknown)
      return std::nullopt;
    return mp_integer{0}; // all operands evaluated to 0
  }
  if(e.id() == ID_bitand || e.id() == ID_and)
  {
    bool any_unknown = false;
    for(const auto &op : e.operands())
    {
      auto v = evaluate(op);
      if(!v.has_value())
        any_unknown = true;
      else if(*v == 0)
        return mp_integer{0}; // AND with 0 is 0
    }
    if(any_unknown)
      return std::nullopt;
    return mp_integer{1};
  }
  if(e.id() == ID_bitxor || e.id() == ID_xor)
  {
    mp_integer acc{0};
    for(const auto &op : e.operands())
    {
      auto v = evaluate(op);
      if(!v.has_value())
        return std::nullopt;
      acc = (acc + *v) % 2;
    }
    return acc;
  }
  if(e.id() == ID_extractbits && e.operands().size() == 2)
  {
    // (extractbits src index) returns a slice of `src` whose width
    // is `e.type()`'s width. When both src and result are 1-bit,
    // and the index is constant, the result equals `src`.
    const auto &eb = to_extractbits_expr(e);
    if(auto bv_out = type_try_dynamic_cast<bitvector_typet>(e.type()))
      if(bv_out->get_width() == 1)
        if(auto bv_in = type_try_dynamic_cast<bitvector_typet>(eb.src().type()))
          if(bv_in->get_width() == 1)
            return evaluate(eb.src());
    return std::nullopt;
  }
  if(e.id() == ID_equal && e.operands().size() == 2)
  {
    auto a = evaluate(e.operands()[0]);
    auto b = evaluate(e.operands()[1]);
    if(a.has_value() && b.has_value())
      return *a == *b ? mp_integer{1} : mp_integer{0};
    return std::nullopt;
  }
  if(e.id() == ID_notequal && e.operands().size() == 2)
  {
    auto a = evaluate(e.operands()[0]);
    auto b = evaluate(e.operands()[1]);
    if(a.has_value() && b.has_value())
      return *a != *b ? mp_integer{1} : mp_integer{0};
    return std::nullopt;
  }
  return std::nullopt;
}

void tseitin_propagatort::enforce(const exprt &e, const mp_integer &value)
{
  if(contradiction)
    return;

  // Symbol case: record value, propagate through definition.
  if(e.id() == ID_symbol && is_bool_typed(e.type()))
  {
    const auto &id = to_symbol_expr(e).get_identifier();
    auto it = known.find(id);
    if(it != known.end())
    {
      if(it->second != value)
        contradiction = true;
      return;
    }
    known[id] = value;
    auto def_it = defs.find(id);
    if(def_it != defs.end())
      enforce(def_it->second, value);
    return;
  }

  // Constant case: just check consistency.
  if(auto v = as_const(e))
  {
    if(*v != value)
      contradiction = true;
    return;
  }

  // (bitnot a) = v  ⟹  a = 1 - v  (for 1-bit / bool a)
  if((e.id() == ID_bitnot || e.id() == ID_not) && e.operands().size() == 1)
  {
    enforce(e.operands()[0], mp_integer{1} - value);
    return;
  }

  // (bitor a b ...) = 0  ⟹  each operand = 0
  if(
    (e.id() == ID_bitor || e.id() == ID_or) && e.operands().size() >= 1 &&
    value == 0)
  {
    for(const auto &op : e.operands())
      enforce(op, mp_integer{0});
    return;
  }

  // (bitand a b ...) = 1  ⟹  each operand = 1
  if(
    (e.id() == ID_bitand || e.id() == ID_and) && e.operands().size() >= 1 &&
    value == 1)
  {
    for(const auto &op : e.operands())
      enforce(op, mp_integer{1});
    return;
  }

  // (bitxor a b) = v: if one operand is determined, propagate to
  // the other.
  if((e.id() == ID_bitxor || e.id() == ID_xor) && e.operands().size() == 2)
  {
    auto a = evaluate(e.operands()[0]);
    auto b = evaluate(e.operands()[1]);
    if(a.has_value() && !b.has_value())
      enforce(e.operands()[1], (value + *a) % 2);
    else if(b.has_value() && !a.has_value())
      enforce(e.operands()[0], (value + *b) % 2);
    return;
  }

  // (extractbits src index) = v with 1-bit src and 1-bit result
  //   ⟹ src = v
  if(e.id() == ID_extractbits && e.operands().size() == 2)
  {
    const auto &eb = to_extractbits_expr(e);
    if(auto bv_out = type_try_dynamic_cast<bitvector_typet>(e.type()))
      if(bv_out->get_width() == 1)
        if(auto bv_in = type_try_dynamic_cast<bitvector_typet>(eb.src().type()))
          if(bv_in->get_width() == 1)
            enforce(eb.src(), value);
    return;
  }

  // (= a b) = v: if v == 1, a = b; if v == 0, a ≠ b.
  if(e.id() == ID_equal && e.operands().size() == 2)
  {
    const auto &lhs = e.operands()[0];
    const auto &rhs = e.operands()[1];

    auto is_polynomial_bv = [](const typet &t)
    {
      if(auto bv = type_try_dynamic_cast<bitvector_typet>(t))
        return bv->get_width() > 1;
      return false;
    };

    // Multi-bit BV equality: emit polynomial dis/equality.
    if(is_polynomial_bv(lhs.type()) && is_polynomial_bv(rhs.type()))
    {
      if(value == 1)
        implied_equalities.emplace_back(lhs, rhs);
      else
        implied_disequalities.emplace_back(lhs, rhs);
      return;
    }

    // 1-bit / boolean equality: reduces to bvxor / not-bvxor.
    if(is_bool_typed(lhs.type()) && is_bool_typed(rhs.type()))
    {
      // (a = b) = 1 ⟹ a == b. (a = b) = 0 ⟹ a != b.
      // If we know one side, propagate to the other.
      auto a = evaluate(lhs);
      auto b = evaluate(rhs);
      if(value == 1)
      {
        if(a.has_value() && !b.has_value())
          enforce(rhs, *a);
        else if(b.has_value() && !a.has_value())
          enforce(lhs, *b);
      }
      else
      {
        if(a.has_value() && !b.has_value())
          enforce(rhs, mp_integer{1} - *a);
        else if(b.has_value() && !a.has_value())
          enforce(lhs, mp_integer{1} - *b);
      }
    }
    return;
  }

  // (notequal a b) = v: same as (equal a b) = 1 - v.
  if(e.id() == ID_notequal && e.operands().size() == 2)
  {
    enforce(
      equal_exprt(e.operands()[0], e.operands()[1]), mp_integer{1} - value);
    return;
  }

  // (ite c t f) = v: if c is known, propagate to the relevant branch.
  if(e.id() == ID_if && e.operands().size() == 3)
  {
    auto c = evaluate(e.operands()[0]);
    if(c.has_value())
    {
      if(*c != 0)
        enforce(e.operands()[1], value);
      else
        enforce(e.operands()[2], value);
    }
    return;
  }
}

void tseitin_propagatort::propagate()
{
  // Forward + backward propagation to a fixed point. Each round:
  //   (a) for each def, evaluate the rhs and add to known if it
  //       reduces to a constant;
  //   (b) for each known sym with an unprocessed def, enforce the
  //       def to that value.
  // Track a set of syms whose def we've already enforced to avoid
  // re-doing work.
  std::unordered_set<irep_idt, irep_id_hash> enforced;
  bool changed = true;
  while(changed && !contradiction)
  {
    changed = false;
    // (a) Forward simplification.
    for(const auto &kv : defs)
    {
      if(known.find(kv.first) != known.end())
        continue;
      auto v = evaluate(kv.second);
      if(v.has_value())
      {
        known[kv.first] = *v;
        changed = true;
      }
    }
    // (b) Backward inversion through definitions.
    for(const auto &kv : known)
    {
      if(enforced.find(kv.first) != enforced.end())
        continue;
      auto def_it = defs.find(kv.first);
      if(def_it == defs.end())
        continue;
      enforced.insert(kv.first);
      enforce(def_it->second, kv.second);
      changed = true;
    }
  }
}

void tseitin_propagatort::run(const std::vector<exprt> &equalities)
{
  for(const auto &eq : equalities)
  {
    if(eq.id() != ID_equal || eq.operands().size() != 2)
      continue;
    ingest(to_equal_expr(eq));
    if(contradiction)
      return;
  }
  propagate();

  // Deduplicate emitted dis/equalities. Backward inversion can
  // emit the same `(= X Y)` more than once when multiple chains
  // converge; feeding duplicates to the algebraic solver
  // multiplies Buchberger work for no extra refutation power.
  auto dedup = [](std::vector<equal_exprt> &v)
  {
    auto less = [](const equal_exprt &a, const equal_exprt &b)
    {
      if(a.lhs() != b.lhs())
        return a.lhs() < b.lhs();
      return a.rhs() < b.rhs();
    };
    auto eq = [](const equal_exprt &a, const equal_exprt &b)
    { return a.lhs() == b.lhs() && a.rhs() == b.rhs(); };
    std::sort(v.begin(), v.end(), less);
    v.erase(std::unique(v.begin(), v.end(), eq), v.end());
  };
  dedup(implied_equalities);
  dedup(implied_disequalities);
}
