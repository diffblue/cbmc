/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex_state.h"

#include <cstdlib>
#include <iostream>

#include <util/base_exceptions.h>
#include <util/exception_utils.h>
#include <util/invariant.h>
#include <util/prefix.h>
#include <util/std_expr.h>

#include <analyses/dirty.h>

goto_symex_statet::goto_symex_statet()
  : depth(0),
    symex_target(nullptr),
    atomic_section_id(0),
    record_events(true),
    dirty()
{
  threads.resize(1);
  new_frame();
}

goto_symex_statet::~goto_symex_statet()=default;

void goto_symex_statet::level0t::operator()(
  ssa_exprt &ssa_expr,
  const namespacet &ns,
  unsigned thread_nr)
{
  // already renamed?
  if(!ssa_expr.get_level_0().empty())
    return;

  const irep_idt &obj_identifier=ssa_expr.get_object_name();

  // guards are not L0-renamed
  if(obj_identifier=="goto_symex::\\guard")
    return;

  const symbolt *s;
  const bool found_l0 = !ns.lookup(obj_identifier, s);
  INVARIANT(found_l0, "level0: failed to find " + id2string(obj_identifier));

  // don't rename shared variables or functions
  if(s->type.id()==ID_code ||
     s->is_shared())
    return;

  // rename!
  ssa_expr.set_level_0(thread_nr);
}

void goto_symex_statet::level1t::operator()(ssa_exprt &ssa_expr)
{
  // already renamed?
  if(!ssa_expr.get_level_1().empty())
    return;

  const irep_idt l0_name=ssa_expr.get_l1_object_identifier();

  current_namest::const_iterator it=current_names.find(l0_name);
  if(it==current_names.end())
    return;

  // rename!
  ssa_expr.set_level_1(it->second.second);
}

/// This function determines what expressions are to be propagated as
/// "constants"
bool goto_symex_statet::constant_propagation(const exprt &expr) const
{
  if(expr.is_constant())
    return true;

  if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(expr);

    return constant_propagation_reference(address_of_expr.object());
  }
  else if(expr.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr=to_typecast_expr(expr);

    return constant_propagation(typecast_expr.op());
  }
  else if(expr.id()==ID_plus)
  {
    forall_operands(it, expr)
      if(!constant_propagation(*it))
        return false;

    return true;
  }
  else if(expr.id()==ID_mult)
  {
    // propagate stuff with sizeof in it
    forall_operands(it, expr)
    {
      if(it->find(ID_C_c_sizeof_type).is_not_nil())
        return true;
      else if(!constant_propagation(*it))
        return false;
    }

    return true;
  }
  else if(expr.id()==ID_array)
  {
    forall_operands(it, expr)
      if(!constant_propagation(*it))
        return false;

    return true;
  }
  else if(expr.id()==ID_array_of)
  {
    return constant_propagation(expr.op0());
  }
  else if(expr.id()==ID_with)
  {
    // this is bad
    /*
    forall_operands(it, expr)
      if(!constant_propagation(expr.op0()))
        return false;

    return true;
    */
    return false;
  }
  else if(expr.id()==ID_struct)
  {
    forall_operands(it, expr)
      if(!constant_propagation(*it))
        return false;

    return true;
  }
  else if(expr.id()==ID_union)
  {
    forall_operands(it, expr)
      if(!constant_propagation(*it))
        return false;

    return true;
  }
  // byte_update works, byte_extract may be out-of-bounds
  else if(expr.id()==ID_byte_update_big_endian ||
          expr.id()==ID_byte_update_little_endian)
  {
    forall_operands(it, expr)
      if(!constant_propagation(*it))
        return false;

    return true;
  }

  return false;
}

/// this function determines which reference-typed expressions are constant
bool goto_symex_statet::constant_propagation_reference(const exprt &expr) const
{
  if(expr.id()==ID_symbol)
    return true;
  else if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);

    return constant_propagation_reference(index_expr.array()) &&
           constant_propagation(index_expr.index());
  }
  else if(expr.id()==ID_member)
  {
    return constant_propagation_reference(to_member_expr(expr).compound());
  }
  else if(expr.id()==ID_string_constant)
    return true;

  return false;
}

/// write to a variable
static bool check_renaming(const exprt &expr);

static bool check_renaming(const typet &type)
{
  if(type.id()==ID_array)
    return check_renaming(to_array_type(type).size());
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_class)
  {
    for(const auto &c : to_struct_union_type(type).components())
      if(check_renaming(c.type()))
        return true;
  }
  else if(type.has_subtype())
    return check_renaming(type.subtype());

  return false;
}

static bool check_renaming_l1(const exprt &expr)
{
  if(check_renaming(expr.type()))
    return true;

  if(expr.id()==ID_symbol)
  {
    if(!expr.get_bool(ID_C_SSA_symbol))
      return expr.type().id()!=ID_code;
    if(!to_ssa_expr(expr).get_level_2().empty())
      return true;
    if(to_ssa_expr(expr).get_original_expr().type()!=expr.type())
      return true;
  }
  else
  {
    forall_operands(it, expr)
      if(check_renaming_l1(*it))
        return true;
  }

  return false;
}

static bool check_renaming(const exprt &expr)
{
  if(check_renaming(expr.type()))
    return true;

  if(expr.id()==ID_address_of &&
     expr.op0().id()==ID_symbol)
    return check_renaming_l1(expr.op0());
  else if(expr.id()==ID_address_of &&
          expr.op0().id()==ID_index)
    return check_renaming_l1(expr.op0().op0()) ||
           check_renaming(expr.op0().op1());
  else if(expr.id()==ID_symbol)
  {
    if(!expr.get_bool(ID_C_SSA_symbol))
      return expr.type().id()!=ID_code;
    if(to_ssa_expr(expr).get_level_2().empty())
      return true;
    if(to_ssa_expr(expr).get_original_expr().type()!=expr.type())
      return true;
  }
  else
  {
    forall_operands(it, expr)
      if(check_renaming(*it))
        return true;
  }

  return false;
}

static void assert_l1_renaming(const exprt &expr)
{
  #if 1
  if(check_renaming_l1(expr))
  {
    std::cerr << expr.pretty() << '\n';
    UNREACHABLE;
  }
  #else
  (void)expr;
  #endif
}

static void assert_l2_renaming(const exprt &expr)
{
  #if 1
  if(check_renaming(expr))
  {
    std::cerr << expr.pretty() << '\n';
    UNREACHABLE;
  }
  #else
  (void)expr;
  #endif
}

void goto_symex_statet::assignment(
  ssa_exprt &lhs, // L0/L1
  const exprt &rhs,  // L2
  const namespacet &ns,
  bool rhs_is_simplified,
  bool record_value,
  bool allow_pointer_unsoundness)
{
  // identifier should be l0 or l1, make sure it's l1
  rename(lhs, ns, L1);
  irep_idt l1_identifier=lhs.get_identifier();

  // the type might need renaming
  rename(lhs.type(), l1_identifier, ns);
  lhs.update_type();
  assert_l1_renaming(lhs);

  #if 0
  PRECONDITION(l1_identifier != get_original_name(l1_identifier)
      || l1_identifier=="goto_symex::\\guard"
      || ns.lookup(l1_identifier).is_shared()
      || has_prefix(id2string(l1_identifier), "symex::invalid_object")
      || has_prefix(id2string(l1_identifier), "symex_dynamic::dynamic_object"));
  #endif

  // do the l2 renaming
  if(level2.current_names.find(l1_identifier)==level2.current_names.end())
    level2.current_names[l1_identifier]=std::make_pair(lhs, 0);
  level2.increase_counter(l1_identifier);
  set_ssa_indices(lhs, ns, L2);

  // in case we happen to be multi-threaded, record the memory access
  bool is_shared=l2_thread_write_encoding(lhs, ns);

  assert_l2_renaming(lhs);
  assert_l2_renaming(rhs);

  // see #305 on GitHub for a simple example and possible discussion
  if(is_shared && lhs.type().id() == ID_pointer && !allow_pointer_unsoundness)
    throw unsupported_operation_exceptiont(
      "pointer handling for concurrency is unsound");

  // for value propagation -- the RHS is L2

  if(!is_shared && record_value && constant_propagation(rhs))
    propagation.values[l1_identifier]=rhs;
  else
    propagation.remove(l1_identifier);

  {
    // update value sets
    value_sett::expr_sett rhs_value_set;
    exprt l1_rhs(rhs);
    get_l1_name(l1_rhs);

    ssa_exprt l1_lhs(lhs);
    get_l1_name(l1_lhs);

    assert_l1_renaming(l1_lhs);
    assert_l1_renaming(l1_rhs);

    value_set.assign(l1_lhs, l1_rhs, ns, rhs_is_simplified, is_shared);
  }

  #if 0
  std::cout << "Assigning " << l1_identifier << '\n';
  value_set.output(ns, std::cout);
  std::cout << "**********************\n";
  #endif
}

void goto_symex_statet::propagationt::operator()(exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    valuest::const_iterator it =
      values.find(to_symbol_expr(expr).get_identifier());
    if(it!=values.end())
      expr=it->second;
  }
  else if(expr.id()==ID_address_of)
  {
    // ignore
  }
  else
  {
    // do this recursively
    Forall_operands(it, expr)
      operator()(*it);
  }
}

void goto_symex_statet::set_ssa_indices(
  ssa_exprt &ssa_expr,
  const namespacet &ns,
  levelt level)
{
  switch(level)
  {
  case L0:
    level0(ssa_expr, ns, source.thread_nr);
    break;

  case L1:
    if(!ssa_expr.get_level_2().empty())
      return;
    if(!ssa_expr.get_level_1().empty())
      return;
    level0(ssa_expr, ns, source.thread_nr);
    level1(ssa_expr);
    break;

  case L2:
    if(!ssa_expr.get_level_2().empty())
      return;
    level0(ssa_expr, ns, source.thread_nr);
    level1(ssa_expr);
    ssa_expr.set_level_2(level2.current_count(ssa_expr.get_identifier()));
    break;

  default:
    UNREACHABLE;
  }
}

void goto_symex_statet::rename(
  exprt &expr,
  const namespacet &ns,
  levelt level)
{
  // rename all the symbols with their last known value

  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
  {
    ssa_exprt &ssa=to_ssa_expr(expr);

    if(level==L0 || level==L1)
    {
      set_ssa_indices(ssa, ns, level);
      rename(expr.type(), ssa.get_identifier(), ns, level);
      ssa.update_type();
    }
    else if(level==L2)
    {
      set_ssa_indices(ssa, ns, L1);
      rename(expr.type(), ssa.get_identifier(), ns, level);
      ssa.update_type();

      if(l2_thread_read_encoding(ssa, ns))
      {
        // renaming taken care of by l2_thread_encoding
      }
      else if(!ssa.get_level_2().empty())
      {
        // already at L2
      }
      else
      {
        // We also consider propagation if we go up to L2.
        // L1 identifiers are used for propagation!
        propagationt::valuest::const_iterator p_it=
          propagation.values.find(ssa.get_identifier());

        if(p_it!=propagation.values.end())
          expr=p_it->second; // already L2
        else
          set_ssa_indices(ssa, ns, L2);
      }
    }
  }
  else if(expr.id()==ID_symbol)
  {
    // we never rename function symbols
    if(ns.follow(expr.type()).id()==ID_code)
    {
      rename(
        expr.type(),
        to_symbol_expr(expr).get_identifier(),
        ns,
        level);

      return;
    }

    expr=ssa_exprt(expr);
    rename(expr, ns, level);
  }
  else if(expr.id()==ID_address_of)
  {
    auto &address_of_expr = to_address_of_expr(expr);
    rename_address(address_of_expr.object(), ns, level);
    expr.type().subtype() = address_of_expr.object().type();
  }
  else
  {
    // this could go wrong, but we would have to re-typecheck ...
    rename(expr.type(), irep_idt(), ns, level);

    // do this recursively
    Forall_operands(it, expr)
      rename(*it, ns, level);

    // some fixes
    if(expr.id()==ID_with)
      expr.type()=to_with_expr(expr).old().type();
    else if(expr.id()==ID_if)
    {
      DATA_INVARIANT(
        to_if_expr(expr).true_case().type() ==
          to_if_expr(expr).false_case().type(),
        "true case of to_if_expr should be of same type "
        "as false case");
      expr.type()=to_if_expr(expr).true_case().type();
    }
  }
}

/// thread encoding
bool goto_symex_statet::l2_thread_read_encoding(
  ssa_exprt &expr,
  const namespacet &ns)
{
  // do we have threads?
  if(threads.size()<=1)
    return false;

  // is it a shared object?
  const irep_idt &obj_identifier=expr.get_object_name();
  if(
    obj_identifier == "goto_symex::\\guard" ||
    (!ns.lookup(obj_identifier).is_shared() && !(dirty)(obj_identifier)))
    return false;

  ssa_exprt ssa_l1=expr;
  ssa_l1.remove_level_2();
  const irep_idt &l1_identifier=ssa_l1.get_identifier();

  // see whether we are within an atomic section
  if(atomic_section_id!=0)
  {
    guardt write_guard;
    write_guard.add(false_exprt());

    written_in_atomic_sectiont::const_iterator a_s_writes=
      written_in_atomic_section.find(ssa_l1);
    if(a_s_writes!=written_in_atomic_section.end())
    {
      for(a_s_w_entryt::const_iterator it=a_s_writes->second.begin();
          it!=a_s_writes->second.end();
          ++it)
      {
        guardt g=*it;
        g-=guard;
        if(g.is_true())
          // there has already been a write to l1_identifier within
          // this atomic section under the same guard, or a guard
          // that implies the current one
          return false;

        write_guard|=*it;
      }
    }

    not_exprt no_write(write_guard.as_expr());

    // we cannot determine for sure that there has been a write already
    // so generate a read even if l1_identifier has been written on
    // all branches flowing into this read
    guardt read_guard;
    read_guard.add(false_exprt());

    a_s_r_entryt &a_s_read=read_in_atomic_section[ssa_l1];
    for(std::list<guardt>::const_iterator it=a_s_read.second.begin();
        it!=a_s_read.second.end();
        ++it)
    {
      guardt g=*it;
      g-=guard;
      if(g.is_true())
        // there has already been a read l1_identifier within
        // this atomic section under the same guard, or a guard
        // that implies the current one
        return false;

      read_guard|=*it;
    }

    exprt cond=read_guard.as_expr();
    if(!no_write.op().is_false())
      cond=or_exprt(no_write.op(), cond);

    if_exprt tmp(cond, ssa_l1, ssa_l1);
    set_ssa_indices(to_ssa_expr(tmp.true_case()), ns, L2);

    if(a_s_read.second.empty())
    {
      if(level2.current_names.find(l1_identifier)==level2.current_names.end())
        level2.current_names[l1_identifier]=std::make_pair(ssa_l1, 0);
      level2.increase_counter(l1_identifier);
      a_s_read.first=level2.current_count(l1_identifier);
    }

    to_ssa_expr(tmp.false_case()).set_level_2(a_s_read.first);

    if(cond.is_false())
    {
      exprt t=tmp.false_case();
      t.swap(tmp);
    }

    const bool record_events_bak=record_events;
    record_events=false;
    assignment(ssa_l1, tmp, ns, true, true);
    record_events=record_events_bak;

    symex_target->assignment(
      guard.as_expr(),
      ssa_l1,
      ssa_l1,
      ssa_l1.get_original_expr(),
      tmp,
      source,
      symex_targett::assignment_typet::PHI);

    set_ssa_indices(ssa_l1, ns, L2);
    expr=ssa_l1;

    a_s_read.second.push_back(guard);
    if(!no_write.op().is_false())
      a_s_read.second.back().add(no_write);

    return true;
  }

  if(level2.current_names.find(l1_identifier)==level2.current_names.end())
    level2.current_names[l1_identifier]=std::make_pair(ssa_l1, 0);

  // No event and no fresh index, but avoid constant propagation
  if(!record_events)
  {
    set_ssa_indices(ssa_l1, ns, L2);
    expr=ssa_l1;
    return true;
  }

  // produce a fresh L2 name
  level2.increase_counter(l1_identifier);
  set_ssa_indices(ssa_l1, ns, L2);
  expr=ssa_l1;

  // and record that
  INVARIANT_STRUCTURED(
    symex_target!=nullptr, nullptr_exceptiont, "symex_target is null");
  symex_target->shared_read(
    guard.as_expr(),
    expr,
    atomic_section_id,
    source);

  return true;
}

/// thread encoding
bool goto_symex_statet::l2_thread_write_encoding(
  const ssa_exprt &expr,
  const namespacet &ns)
{
  if(!record_events)
    return false;

  // is it a shared object?
  const irep_idt &obj_identifier=expr.get_object_name();
  if(
    obj_identifier == "goto_symex::\\guard" ||
    (!ns.lookup(obj_identifier).is_shared() && !(dirty)(obj_identifier)))
    return false; // not shared

  // see whether we are within an atomic section
  if(atomic_section_id!=0)
  {
    ssa_exprt ssa_l1=expr;
    ssa_l1.remove_level_2();

    written_in_atomic_section[ssa_l1].push_back(guard);
    return false;
  }

  // record a shared write
  symex_target->shared_write(
    guard.as_expr(),
    expr,
    atomic_section_id,
    source);

  // do we have threads?
  return threads.size()>1;
}

void goto_symex_statet::rename_address(
  exprt &expr,
  const namespacet &ns,
  levelt level)
{
  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
  {
    ssa_exprt &ssa=to_ssa_expr(expr);

    // only do L1!
    set_ssa_indices(ssa, ns, L1);

    rename(expr.type(), ssa.get_identifier(), ns, level);
    ssa.update_type();
  }
  else if(expr.id()==ID_symbol)
  {
    expr=ssa_exprt(expr);
    rename_address(expr, ns, level);
  }
  else
  {
    if(expr.id()==ID_index)
    {
      index_exprt &index_expr=to_index_expr(expr);

      rename_address(index_expr.array(), ns, level);
      PRECONDITION(index_expr.array().type().id() == ID_array);
      expr.type()=index_expr.array().type().subtype();

      // the index is not an address
      rename(index_expr.index(), ns, level);
    }
    else if(expr.id()==ID_if)
    {
      // the condition is not an address
      if_exprt &if_expr=to_if_expr(expr);
      rename(if_expr.cond(), ns, level);
      rename_address(if_expr.true_case(), ns, level);
      rename_address(if_expr.false_case(), ns, level);

      if_expr.type()=if_expr.true_case().type();
    }
    else if(expr.id()==ID_member)
    {
      member_exprt &member_expr=to_member_expr(expr);

      rename_address(member_expr.struct_op(), ns, level);

      // type might not have been renamed in case of nesting of
      // structs and pointers/arrays
      if(
        member_expr.struct_op().type().id() != ID_symbol_type &&
        member_expr.struct_op().type().id() != ID_struct_tag &&
        member_expr.struct_op().type().id() != ID_union_tag)
      {
        const struct_union_typet &su_type=
          to_struct_union_type(member_expr.struct_op().type());
        const struct_union_typet::componentt &comp=
          su_type.get_component(member_expr.get_component_name());
        PRECONDITION(comp.is_not_nil());
        expr.type()=comp.type();
      }
      else
        rename(expr.type(), irep_idt(), ns, level);
    }
    else
    {
      // this could go wrong, but we would have to re-typecheck ...
      rename(expr.type(), irep_idt(), ns, level);

      // do this recursively; we assume here
      // that all the operands are addresses
      Forall_operands(it, expr)
        rename_address(*it, ns, level);
    }
  }
}

void goto_symex_statet::rename(
  typet &type,
  const irep_idt &l1_identifier,
  const namespacet &ns,
  levelt level)
{
  // rename all the symbols with their last known value
  // to the given level

  std::pair<l1_typest::iterator, bool> l1_type_entry;
  if(level==L2 &&
     !l1_identifier.empty())
  {
    l1_type_entry=l1_types.insert(std::make_pair(l1_identifier, type));

    if(!l1_type_entry.second) // was already in map
    {
      // do not change a complete array type to an incomplete one

      const typet &type_prev=l1_type_entry.first->second;

      if(type.id()!=ID_array ||
         type_prev.id()!=ID_array ||
         to_array_type(type).is_incomplete() ||
         to_array_type(type_prev).is_complete())
      {
        type=l1_type_entry.first->second;
        return;
      }
    }
  }

  if(type.id()==ID_array)
  {
    rename(type.subtype(), irep_idt(), ns, level);
    rename(to_array_type(type).size(), ns, level);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_class)
  {
    struct_union_typet &s_u_type=to_struct_union_type(type);
    struct_union_typet::componentst &components=s_u_type.components();

    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        ++it)
      // be careful, or it might get cyclic
      if(it->type().id()==ID_array)
        rename(to_array_type(it->type()).size(), ns, level);
      else if(it->type().id()!=ID_pointer)
        rename(it->type(), irep_idt(), ns, level);
  }
  else if(type.id()==ID_pointer)
  {
    rename(type.subtype(), irep_idt(), ns, level);
  }
  else if(type.id() == ID_symbol_type)
  {
    const symbolt &symbol = ns.lookup(to_symbol_type(type));
    type = symbol.type;
    rename(type, l1_identifier, ns, level);
  }
  else if(type.id() == ID_union_tag)
  {
    const symbolt &symbol = ns.lookup(to_union_tag_type(type));
    type = symbol.type;
    rename(type, l1_identifier, ns, level);
  }
  else if(type.id() == ID_struct_tag)
  {
    const symbolt &symbol = ns.lookup(to_struct_tag_type(type));
    type=symbol.type;
    rename(type, l1_identifier, ns, level);
  }

  if(level==L2 &&
     !l1_identifier.empty())
    l1_type_entry.first->second=type;
}

void goto_symex_statet::get_original_name(exprt &expr) const
{
  get_original_name(expr.type());

  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
    expr=to_ssa_expr(expr).get_original_expr();
  else
    Forall_operands(it, expr)
      get_original_name(*it);
}

void goto_symex_statet::get_original_name(typet &type) const
{
  // rename all the symbols with their last known value

  if(type.id()==ID_array)
  {
    get_original_name(type.subtype());
    get_original_name(to_array_type(type).size());
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union ||
          type.id()==ID_class)
  {
    struct_union_typet &s_u_type=to_struct_union_type(type);
    struct_union_typet::componentst &components=s_u_type.components();

    for(struct_union_typet::componentst::iterator
        it=components.begin();
        it!=components.end();
        ++it)
      get_original_name(it->type());
  }
  else if(type.id()==ID_pointer)
  {
    get_original_name(type.subtype());
  }
}

void goto_symex_statet::get_l1_name(exprt &expr) const
{
  // do not reset the type !

  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
    to_ssa_expr(expr).remove_level_2();
  else
    Forall_operands(it, expr)
      get_l1_name(*it);
}

void goto_symex_statet::switch_to_thread(unsigned t)
{
  PRECONDITION(source.thread_nr < threads.size());
  PRECONDITION(t < threads.size());

  // save PC
  threads[source.thread_nr].pc=source.pc;
  threads[source.thread_nr].atomic_section_id=atomic_section_id;

  // get new PC
  source.thread_nr=t;
  source.pc=threads[t].pc;

  guard=threads[t].guard;
}
