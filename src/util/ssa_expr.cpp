/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ssa_expr.h"

#include <sstream>

#include "pointer_expr.h"

/// If \p expr is:
/// - a symbol_exprt "s" add "s" to the stream \p os
///   - a member_exprt, apply recursively and add "..component_name"
///   - an index_exprt where the index is a constant, apply recursively on the
///     array and add "[[index]]"
/// \return the stream \p os
static std::ostream &
initialize_ssa_identifier(std::ostream &os, const exprt &expr)
{
  if(auto member = expr_try_dynamic_cast<member_exprt>(expr))
  {
    return initialize_ssa_identifier(os, member->struct_op())
           << ".." << member->get_component_name();
  }
  if(auto index = expr_try_dynamic_cast<index_exprt>(expr))
  {
    const irep_idt &idx = to_constant_expr(index->index()).get_value();
    return initialize_ssa_identifier(os, index->array()) << "[[" << idx << "]]";
  }
  if(auto symbol = expr_try_dynamic_cast<symbol_exprt>(expr))
    return os << symbol->get_identifier();

  UNREACHABLE;
}

ssa_exprt::ssa_exprt(const exprt &expr) : symbol_exprt(expr.type())
{
  set(ID_C_SSA_symbol, true);
  add(ID_expression, expr);
  with_source_location(expr.source_location());
  std::ostringstream os;
  initialize_ssa_identifier(os, expr);
  const std::string id = os.str();
  set_identifier(id);
  set(ID_L1_object_identifier, id);
}

/// If \p expr is a symbol "s" add to \p os "s!l0@l1#l2" and to \p l1_object_os
/// "s!l0@l1".
/// If \p expr is a member or index expression, recursively apply the procedure
/// and add "..component_name" or "[[index]]" to \p os.
static void build_ssa_identifier_rec(
  const exprt &expr,
  const irep_idt &l0,
  const irep_idt &l1,
  const irep_idt &l2,
  std::ostream &os,
  std::ostream &l1_object_os)
{
  if(expr.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(expr);

    build_ssa_identifier_rec(member.struct_op(), l0, l1, l2, os, l1_object_os);

    os << ".." << member.get_component_name();
    l1_object_os << ".." << member.get_component_name();
  }
  else if(expr.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(expr);

    build_ssa_identifier_rec(index.array(), l0, l1, l2, os, l1_object_os);

    const irep_idt &idx = to_constant_expr(index.index()).get_value();
    os << "[[" << idx << "]]";
    l1_object_os << "[[" << idx << "]]";
  }
  else if(expr.id()==ID_symbol)
  {
    auto symid=to_symbol_expr(expr).get_identifier();
    os << symid;
    l1_object_os << symid;

    if(!l0.empty())
    {
      // Distinguish different threads of execution
      os << '!' << l0;
      l1_object_os << '!' << l0;
    }

    if(!l1.empty())
    {
      // Distinguish different calls to the same function (~stack frame)
      os << '@' << l1;
      l1_object_os << '@' << l1;
    }

    if(!l2.empty())
    {
      // Distinguish SSA steps for the same variable
      os << '#' << l2;
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
  std::ostringstream oss;
  std::ostringstream l1_object_oss;

  build_ssa_identifier_rec(expr, l0, l1, l2, oss, l1_object_oss);

  return std::make_pair(irep_idt(oss.str()), irep_idt(l1_object_oss.str()));
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
