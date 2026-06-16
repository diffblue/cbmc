/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ssa_expr.h"

#include "pointer_expr.h"

/// If \p expr is:
/// - a symbol_exprt "s" add "s" to the string \p os
///   - a member_exprt, apply recursively and add "..component_name"
///   - an index_exprt where the index is a constant, apply recursively on the
///     array and add "[[index]]"
///
/// The identifier is assembled by plain string concatenation rather than via a
/// `std::ostringstream`: this function is on symex's hot renaming path, and
/// constructing a stream per call pays a substantial fixed cost (locale
/// initialisation) for what is pure concatenation of already-formatted strings.
static void initialize_ssa_identifier(std::string &os, const exprt &expr)
{
  if(auto member = expr_try_dynamic_cast<member_exprt>(expr))
  {
    initialize_ssa_identifier(os, member->struct_op());
    os += "..";
    os += id2string(member->get_component_name());
    return;
  }
  if(auto index = expr_try_dynamic_cast<index_exprt>(expr))
  {
    initialize_ssa_identifier(os, index->array());
    os += "[[";
    os += id2string(to_constant_expr(index->index()).get_value());
    os += "]]";
    return;
  }
  if(auto symbol = expr_try_dynamic_cast<symbol_exprt>(expr))
  {
    os += id2string(symbol->identifier());
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
  initialize_ssa_identifier(id, expr);
  identifier(id);
  set(ID_L1_object_identifier, id);
}

/// If \p expr is a symbol "s" add to \p os "s!l0@l1#l2" and to \p l1_object_os
/// "s!l0@l1".
/// If \p expr is a member or index expression, recursively apply the procedure
/// and add "..component_name" or "[[index]]" to \p os.
///
/// Uses `std::string` concatenation rather than `std::ostream`: see
/// initialize_ssa_identifier above for the rationale (this is a symex hot path).
static void build_ssa_identifier_rec(
  const exprt &expr,
  const irep_idt &l0,
  const irep_idt &l1,
  const irep_idt &l2,
  std::string &os,
  std::string &l1_object_os)
{
  if(expr.id() == ID_member)
  {
    const member_exprt &member = to_member_expr(expr);

    build_ssa_identifier_rec(member.struct_op(), l0, l1, l2, os, l1_object_os);

    const std::string component = ".." + id2string(member.get_component_name());
    os += component;
    l1_object_os += component;
  }
  else if(expr.id() == ID_index)
  {
    const index_exprt &index = to_index_expr(expr);

    build_ssa_identifier_rec(index.array(), l0, l1, l2, os, l1_object_os);

    const std::string idx =
      "[[" + id2string(to_constant_expr(index.index()).get_value()) + "]]";
    os += idx;
    l1_object_os += idx;
  }
  else if(expr.id() == ID_symbol)
  {
    const irep_idt &symid = to_symbol_expr(expr).identifier();
    os += id2string(symid);
    l1_object_os += id2string(symid);

    if(!l0.empty())
    {
      // Distinguish different threads of execution
      os += '!';
      os += id2string(l0);
      l1_object_os += '!';
      l1_object_os += id2string(l0);
    }

    if(!l1.empty())
    {
      // Distinguish different calls to the same function (~stack frame)
      os += '@';
      os += id2string(l1);
      l1_object_os += '@';
      l1_object_os += id2string(l1);
    }

    if(!l2.empty())
    {
      // Distinguish SSA steps for the same variable
      os += '#';
      os += id2string(l2);
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
  std::string oss;
  std::string l1_object_oss;

  build_ssa_identifier_rec(expr, l0, l1, l2, oss, l1_object_oss);

  return std::make_pair(irep_idt{oss}, irep_idt{l1_object_oss});
}

static void update_identifier(ssa_exprt &ssa)
{
  const irep_idt &l0 = ssa.get_level_0();
  const irep_idt &l1 = ssa.get_level_1();
  const irep_idt &l2 = ssa.get_level_2();

  auto idpair = build_identifier(ssa.get_original_expr(), l0, l1, l2);
  ssa.identifier(idpair.first);
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
    return to_symbol_expr(original_expr).identifier();

  return to_symbol_expr(object_descriptor_exprt::root_object(original_expr))
    .identifier();
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
  ::update_identifier(*this);
}

void ssa_exprt::set_level_1(std::size_t i)
{
  set(ID_L1, i);
  ::update_identifier(*this);
}

void ssa_exprt::set_level_2(std::size_t i)
{
  set(ID_L2, i);
  ::update_identifier(*this);
}

void ssa_exprt::remove_level_2()
{
  remove(ID_L2);
  identifier(get_l1_object_identifier());
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
