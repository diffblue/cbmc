/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ssa_expr.h"

#include "pointer_expr.h"

/// If \p expr is:
/// - a symbol_exprt "s" add "s" to the stream \p os
///   - a member_exprt, apply recursively and add "..component_name"
///   - an index_exprt where the index is a constant, apply recursively on the
///     array and add "[[index]]"
/// \return the stream \p os
static void initialize_ssa_identifier(std::string &id, const exprt &expr)
{
  if(auto member = expr_try_dynamic_cast<member_exprt>(expr))
  {
    initialize_ssa_identifier(id, member->struct_op());
    id += "..";
    id += id2string(member->get_component_name());
    return;
  }
  if(auto index = expr_try_dynamic_cast<index_exprt>(expr))
  {
    initialize_ssa_identifier(id, index->array());
    id += "[[";
    id += id2string(to_constant_expr(index->index()).get_value());
    id += "]]";
    return;
  }
  if(auto symbol = expr_try_dynamic_cast<symbol_exprt>(expr))
  {
    id += id2string(symbol->get_identifier());
    return;
  }

  UNREACHABLE;
}

ssa_exprt::ssa_exprt(const exprt &expr) : symbol_exprt(expr.type())
{
  set(ID_C_SSA_symbol, true);
  add(ID_expression, expr);
  with_source_location(expr.source_location());
  std::string id;
  id.reserve(64);
  initialize_ssa_identifier(id, expr);
  set_identifier(id);
  set(ID_L1_object_identifier, id);
}

/// If \p expr is a symbol "s" add to \p os "s!l0@l1#l2" and to \p l1_object_os
/// "s!l0@l1".
/// If \p expr is a member or index expression, recursively apply the procedure
/// and add "..component_name" or "[[index]]" to \p os.
/// Build the base part of an SSA identifier (without level suffixes)
/// by appending to \p id and \p l1_object_id.
static void build_ssa_identifier_rec(
  const exprt &expr,
  const irep_idt &l0,
  const irep_idt &l1,
  const irep_idt &l2,
  std::string &id,
  std::string &l1_object_id)
{
  if(expr.id() == ID_member)
  {
    const member_exprt &member = to_member_expr(expr);

    build_ssa_identifier_rec(member.struct_op(), l0, l1, l2, id, l1_object_id);

    const std::string &component = id2string(member.get_component_name());
    id += "..";
    id += component;
    l1_object_id += "..";
    l1_object_id += component;
  }
  else if(expr.id() == ID_index)
  {
    const index_exprt &index = to_index_expr(expr);

    build_ssa_identifier_rec(index.array(), l0, l1, l2, id, l1_object_id);

    const std::string &idx =
      id2string(to_constant_expr(index.index()).get_value());
    id += "[[";
    id += idx;
    id += "]]";
    l1_object_id += "[[";
    l1_object_id += idx;
    l1_object_id += "]]";
  }
  else if(expr.id() == ID_symbol)
  {
    const std::string &symid = id2string(to_symbol_expr(expr).get_identifier());
    id += symid;
    l1_object_id += symid;

    if(!l0.empty())
    {
      const std::string &l0s = id2string(l0);
      id += '!';
      id += l0s;
      l1_object_id += '!';
      l1_object_id += l0s;
    }

    if(!l1.empty())
    {
      const std::string &l1s = id2string(l1);
      id += '@';
      id += l1s;
      l1_object_id += '@';
      l1_object_id += l1s;
    }

    if(!l2.empty())
    {
      id += '#';
      id += id2string(l2);
    }
  }
  else
    UNREACHABLE;
}

static std::pair<irep_idt, irep_idt> build_identifier(
  const exprt &expr,
  const irep_idt &l0,
  const irep_idt &l1,
  const irep_idt &l2)
{
  std::string id;
  std::string l1_object_id;
  // Typical SSA identifiers are 20-60 chars; pre-allocate to avoid
  // repeated reallocation during string building.
  id.reserve(64);
  l1_object_id.reserve(64);

  build_ssa_identifier_rec(expr, l0, l1, l2, id, l1_object_id);

  return std::make_pair(irep_idt(id), irep_idt(l1_object_id));
}

static void update_identifier(ssa_exprt &ssa)
{
  const irep_idt &l0 = ssa.get_level_0();
  const irep_idt &l1 = ssa.get_level_1();
  const irep_idt &l2 = ssa.get_level_2();

  auto idpair = build_identifier(ssa.get_original_expr(), l0, l1, l2);
  ssa.set_identifier(idpair.first);
  ssa.set(ID_L1_object_identifier, idpair.second);
}

void ssa_exprt::set_expression(exprt expr)
{
  type() = as_const(expr).type();
  add(ID_expression, std::move(expr));
  ::update_identifier(*this);
}

irep_idt ssa_exprt::get_object_name() const
{
  const exprt &original_expr = get_original_expr();

  if(original_expr.id() == ID_symbol)
    return to_symbol_expr(original_expr).get_identifier();

  return to_symbol_expr(object_descriptor_exprt::root_object(original_expr))
    .get_identifier();
}

const ssa_exprt ssa_exprt::get_l1_object() const
{
  object_descriptor_exprt ode(get_original_expr());

  ssa_exprt root(ode.root_object());
  if(!get_level_0().empty())
    root.set(ID_L0, get(ID_L0));
  if(!get_level_1().empty())
    root.set(ID_L1, get(ID_L1));
  ::update_identifier(root);

  return root;
}

const irep_idt ssa_exprt::get_l1_object_identifier() const
{
#if 0
  return get_l1_object().get_identifier();
#else
  // the above is the clean version, this is the fast one, using
  // an identifier cached during build_identifier
  return get(ID_L1_object_identifier);
#endif
}

void ssa_exprt::set_level_0(std::size_t i)
{
  set(ID_L0, i);
  // Optimized: L0 is only set when it was previously empty (the caller
  // guards against re-setting). The current identifier is "base" and
  // we need "base!l0". Append directly instead of rebuilding.
  const std::string &cur_id = id2string(get_identifier());
  std::string suffix = "!" + std::to_string(i);
  std::string new_id = cur_id + suffix;
  set_identifier(new_id);
  set(ID_L1_object_identifier, new_id);
}

void ssa_exprt::set_level_1(std::size_t i)
{
  set(ID_L1, i);
  // Optimized: L1 is only set when it was previously empty (the caller
  // guards against re-setting). The current identifier is "base!l0" and
  // we need "base!l0@l1". Append directly instead of rebuilding.
  const std::string &cur_id = id2string(get_identifier());
  std::string suffix = "@" + std::to_string(i);
  std::string new_id = cur_id + suffix;
  set_identifier(new_id);
  set(ID_L1_object_identifier, new_id);
}

void ssa_exprt::set_level_2(std::size_t i)
{
  set(ID_L2, i);
  // Optimized: the L1 object identifier doesn't change when only L2 changes,
  // and the main identifier just needs the #N suffix updated. Derive from
  // the cached L1 object identifier instead of rebuilding from scratch.
  const std::string &l1_id = id2string(get(ID_L1_object_identifier));
  std::string new_id;
  new_id.reserve(l1_id.size() + 8);
  new_id = l1_id;
  new_id += '#';
  new_id += std::to_string(i);
  set_identifier(new_id);
}

void ssa_exprt::remove_level_2()
{
  remove(ID_L2);
  set_identifier(get_l1_object_identifier());
}

/* Used to determine whether or not an identifier can be built
   * before trying and getting an exception */
bool ssa_exprt::can_build_identifier(const exprt &expr)
{
  if(expr.id() == ID_symbol)
    return true;
  else if(expr.id() == ID_member)
    return can_build_identifier(to_member_expr(expr).compound());
  else if(expr.id() == ID_index)
    return can_build_identifier(to_index_expr(expr).array());
  else
    return false;
}

ssa_exprt remove_level_2(ssa_exprt ssa)
{
  ssa.remove_level_2();
  return ssa;
}
