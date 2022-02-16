/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex_state.h"
#include "goto_symex_is_constant.h"

#include <iostream>

#include <util/as_const.h>
#include <util/base_exceptions.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/find_symbols.h>
#include <util/invariant.h>
#include <util/std_expr.h>

#include <analyses/dirty.h>
#include <pointer-analysis/add_failed_symbols.h>

static void get_l1_name(exprt &expr);

goto_symex_statet::goto_symex_statet(
  const symex_targett::sourcet &_source,
  std::size_t max_field_sensitive_array_size,
  guard_managert &manager,
  std::function<std::size_t(const irep_idt &)> fresh_l2_name_provider)
  : goto_statet(manager),
    source(_source),
    guard_manager(manager),
    symex_target(nullptr),
    field_sensitivity(max_field_sensitive_array_size),
    record_events({true}),
    fresh_l2_name_provider(fresh_l2_name_provider)
{
  threads.emplace_back(guard_manager);
  call_stack().new_frame(source, guardt(true_exprt(), manager));
}

goto_symex_statet::~goto_symex_statet()=default;

template <>
renamedt<ssa_exprt, L0>
goto_symex_statet::set_indices<L0>(ssa_exprt ssa_expr, const namespacet &ns)
{
  return symex_level0(std::move(ssa_expr), ns, source.thread_nr);
}

template <>
renamedt<ssa_exprt, L1>
goto_symex_statet::set_indices<L1>(ssa_exprt ssa_expr, const namespacet &ns)
{
  return level1(symex_level0(std::move(ssa_expr), ns, source.thread_nr));
}

template <>
renamedt<ssa_exprt, L2>
goto_symex_statet::set_indices<L2>(ssa_exprt ssa_expr, const namespacet &ns)
{
  return level2(
    level1(symex_level0(std::move(ssa_expr), ns, source.thread_nr)));
}

renamedt<ssa_exprt, L2> goto_symex_statet::assignment(
  ssa_exprt lhs,    // L0/L1
  const exprt &rhs, // L2
  const namespacet &ns,
  bool rhs_is_simplified,
  bool record_value,
  bool allow_pointer_unsoundness)
{
  // identifier should be l0 or l1, make sure it's l1
  lhs = rename_ssa<L1>(std::move(lhs), ns).get();
  irep_idt l1_identifier=lhs.get_identifier();

  // the type might need renaming
  rename<L2>(lhs.type(), l1_identifier, ns);
  lhs.update_type();
  if(run_validation_checks)
  {
    DATA_INVARIANT(!check_renaming_l1(lhs), "lhs renaming failed on l1");
  }

  // do the l2 renaming
  level2.increase_generation(l1_identifier, lhs, fresh_l2_name_provider);
  renamedt<ssa_exprt, L2> l2_lhs = set_indices<L2>(std::move(lhs), ns);
  lhs = l2_lhs.get();

  // in case we happen to be multi-threaded, record the memory access
  bool is_shared=l2_thread_write_encoding(lhs, ns);

  if(run_validation_checks)
  {
    DATA_INVARIANT(!check_renaming(lhs), "lhs renaming failed on l2");
    DATA_INVARIANT(!check_renaming(rhs), "rhs renaming failed on l2");
  }

  // see #305 on GitHub for a simple example and possible discussion
  if(is_shared && lhs.type().id() == ID_pointer && !allow_pointer_unsoundness)
    throw unsupported_operation_exceptiont(
      "pointer handling for concurrency is unsound");

  // Update constant propagation map -- the RHS is L2
  if(!is_shared && record_value && goto_symex_is_constantt()(rhs))
  {
    const auto propagation_entry = propagation.find(l1_identifier);
    if(!propagation_entry.has_value())
      propagation.insert(l1_identifier, rhs);
    else if(propagation_entry->get() != rhs)
      propagation.replace(l1_identifier, rhs);
  }
  else
    propagation.erase_if_exists(l1_identifier);

  {
    // update value sets
    exprt l1_rhs(rhs);
    get_l1_name(l1_rhs);

    const ssa_exprt l1_lhs = remove_level_2(lhs);
    if(run_validation_checks)
    {
      DATA_INVARIANT(!check_renaming_l1(l1_lhs), "lhs renaming failed on l1");
      DATA_INVARIANT(!check_renaming_l1(l1_rhs), "rhs renaming failed on l1");
    }

    value_set.assign(l1_lhs, l1_rhs, ns, rhs_is_simplified, is_shared);
  }

#ifdef DEBUG
  std::cout << "Assigning " << l1_identifier << '\n';
  value_set.output(std::cout);
  std::cout << "**********************\n";
#endif

  return l2_lhs;
}

template <levelt level>
renamedt<ssa_exprt, level>
goto_symex_statet::rename_ssa(ssa_exprt ssa, const namespacet &ns)
{
  static_assert(
    level == L0 || level == L1,
    "rename_ssa can only be used for levels L0 and L1");
  ssa = set_indices<level>(std::move(ssa), ns).get();
  rename<level>(ssa.type(), ssa.get_identifier(), ns);
  ssa.update_type();
  return renamedt<ssa_exprt, level>{ssa};
}

/// Ensure `rename_ssa` gets compiled for L0
template renamedt<ssa_exprt, L0>
goto_symex_statet::rename_ssa<L0>(ssa_exprt ssa, const namespacet &ns);
template renamedt<ssa_exprt, L1>
goto_symex_statet::rename_ssa<L1>(ssa_exprt ssa, const namespacet &ns);

template <levelt level>
renamedt<exprt, level>
goto_symex_statet::rename(exprt expr, const namespacet &ns)
{
  // rename all the symbols with their last known value

  static_assert(
    level == L0 || level == L1 || level == L1_WITH_CONSTANT_PROPAGATION ||
      level == L2,
    "must handle all renaming levels");

  if(is_ssa_expr(expr))
  {
    exprt original_expr = expr;
    ssa_exprt &ssa=to_ssa_expr(expr);

    if(level == L0)
    {
      return renamedt<exprt, level>{
        std::move(rename_ssa<L0>(std::move(ssa), ns).value())};
    }
    else if(level == L1)
    {
      return renamedt<exprt, level>{
        std::move(rename_ssa<L1>(std::move(ssa), ns).value())};
    }
    else
    {
      ssa = set_indices<L1>(std::move(ssa), ns).get();
      rename<level>(expr.type(), ssa.get_identifier(), ns);
      ssa.update_type();

      // renaming taken care of by l2_thread_encoding, or already at L2
      if(l2_thread_read_encoding(ssa, ns) || !ssa.get_level_2().empty())
      {
        if(level == L1_WITH_CONSTANT_PROPAGATION)
        {
          // Don't actually rename to L2 -- we just used `ssa` to check whether
          // constant-propagation was applicable
          return renamedt<exprt, level>(std::move(original_expr));
        }
        else
          return renamedt<exprt, level>(std::move(ssa));
      }
      else
      {
        // We also consider propagation if we go up to L2.
        // L1 identifiers are used for propagation!
        auto p_it = propagation.find(ssa.get_identifier());

        if(p_it.has_value())
        {
          return renamedt<exprt, level>(*p_it); // already L2
        }
        else
        {
          if(level == L2)
            ssa = set_indices<L2>(std::move(ssa), ns).get();
          return renamedt<exprt, level>(std::move(ssa));
        }
      }
    }
  }
  else if(expr.id()==ID_symbol)
  {
    const auto &type = as_const(expr).type();

    // we never rename function symbols
    if(type.id() == ID_code || type.id() == ID_mathematical_function)
    {
      rename<level>(expr.type(), to_symbol_expr(expr).get_identifier(), ns);
      return renamedt<exprt, level>{std::move(expr)};
    }
    else
      return rename<level>(ssa_exprt{expr}, ns);
  }
  else if(expr.id()==ID_address_of)
  {
    auto &address_of_expr = to_address_of_expr(expr);
    rename_address<level>(address_of_expr.object(), ns);
    to_pointer_type(expr.type()).base_type() =
      as_const(address_of_expr).object().type();
    return renamedt<exprt, level>{std::move(expr)};
  }
  else if(expr.is_nil())
  {
    return renamedt<exprt, level>{std::move(expr)};
  }
  else
  {
    rename<level>(expr.type(), irep_idt(), ns);

    // do this recursively
    Forall_operands(it, expr)
      *it = rename<level>(std::move(*it), ns).get();

    const exprt &c_expr = as_const(expr);
    INVARIANT(
      (expr.id() != ID_with ||
       c_expr.type() == to_with_expr(c_expr).old().type()) &&
        (expr.id() != ID_if ||
         (c_expr.type() == to_if_expr(c_expr).true_case().type() &&
          c_expr.type() == to_if_expr(c_expr).false_case().type())),
      "Type of renamed expr should be the same as operands for with_exprt and "
      "if_exprt");

    if(level == L2)
      expr = field_sensitivity.apply(ns, *this, std::move(expr), false);

    return renamedt<exprt, level>{std::move(expr)};
  }
}

// Explicitly instantiate the one version of this function without an explicit
// caller in this file:
template renamedt<exprt, L1_WITH_CONSTANT_PROPAGATION>
goto_symex_statet::rename(exprt expr, const namespacet &ns);

exprt goto_symex_statet::l2_rename_rvalues(exprt lvalue, const namespacet &ns)
{
  rename(lvalue.type(), irep_idt(), ns);

  if(lvalue.id() == ID_symbol)
  {
    // Nothing to do
  }
  else if(is_read_only_object(lvalue))
  {
    // Ignore apparent writes to 'NULL-object' and similar read-only objects
  }
  else if(lvalue.id() == ID_typecast)
  {
    auto &typecast_lvalue = to_typecast_expr(lvalue);
    typecast_lvalue.op() = l2_rename_rvalues(typecast_lvalue.op(), ns);
  }
  else if(lvalue.id() == ID_member)
  {
    auto &member_lvalue = to_member_expr(lvalue);
    member_lvalue.compound() = l2_rename_rvalues(member_lvalue.compound(), ns);
  }
  else if(lvalue.id() == ID_index)
  {
    // The index is an rvalue:
    auto &index_lvalue = to_index_expr(lvalue);
    index_lvalue.array() = l2_rename_rvalues(index_lvalue.array(), ns);
    index_lvalue.index() = rename(index_lvalue.index(), ns).get();
  }
  else if(
    lvalue.id() == ID_byte_extract_little_endian ||
    lvalue.id() == ID_byte_extract_big_endian)
  {
    // The offset is an rvalue:
    auto &byte_extract_lvalue = to_byte_extract_expr(lvalue);
    byte_extract_lvalue.op() = l2_rename_rvalues(byte_extract_lvalue.op(), ns);
    byte_extract_lvalue.offset() = rename(byte_extract_lvalue.offset(), ns);
  }
  else if(lvalue.id() == ID_if)
  {
    // The condition is an rvalue:
    auto &if_lvalue = to_if_expr(lvalue);
    if_lvalue.cond() = rename(if_lvalue.cond(), ns);
    if(!if_lvalue.cond().is_false())
      if_lvalue.true_case() = l2_rename_rvalues(if_lvalue.true_case(), ns);
    if(!if_lvalue.cond().is_true())
      if_lvalue.false_case() = l2_rename_rvalues(if_lvalue.false_case(), ns);
  }
  else if(lvalue.id() == ID_complex_real)
  {
    auto &complex_real_lvalue = to_complex_real_expr(lvalue);
    complex_real_lvalue.op() = l2_rename_rvalues(complex_real_lvalue.op(), ns);
  }
  else if(lvalue.id() == ID_complex_imag)
  {
    auto &complex_imag_lvalue = to_complex_imag_expr(lvalue);
    complex_imag_lvalue.op() = l2_rename_rvalues(complex_imag_lvalue.op(), ns);
  }
  else
  {
    throw unsupported_operation_exceptiont(
      "l2_rename_rvalues case `" + lvalue.id_string() + "' not handled");
  }

  return lvalue;
}

template renamedt<exprt, L1>
goto_symex_statet::rename<L1>(exprt expr, const namespacet &ns);

/// thread encoding
bool goto_symex_statet::l2_thread_read_encoding(
  ssa_exprt &expr,
  const namespacet &ns)
{
  // do we have threads?
  if(threads.size()<=1)
    return false;

  // is it a shared object?
  PRECONDITION(dirty != nullptr);
  const irep_idt &obj_identifier=expr.get_object_name();
  if(
    obj_identifier == guard_identifier() ||
    (!ns.lookup(obj_identifier).is_shared() && !(*dirty)(obj_identifier)))
  {
    return false;
  }

  // only continue if an indivisible object is being accessed
  if(field_sensitivity.is_divisible(expr))
    return false;

  const ssa_exprt ssa_l1 = remove_level_2(expr);
  const irep_idt &l1_identifier=ssa_l1.get_identifier();
  const exprt guard_as_expr = guard.as_expr();

  // see whether we are within an atomic section
  if(atomic_section_id!=0)
  {
    guardt write_guard{false_exprt{}, guard_manager};

    const auto a_s_writes = written_in_atomic_section.find(ssa_l1);
    if(a_s_writes!=written_in_atomic_section.end())
    {
      for(const auto &guard_in_list : a_s_writes->second)
      {
        guardt g = guard_in_list;
        g-=guard;
        if(g.is_true())
          // There has already been a write to l1_identifier within this atomic
          // section under the same guard, or a guard implied by the current
          // one.
          return false;

        write_guard |= guard_in_list;
      }
    }

    not_exprt no_write(write_guard.as_expr());

    // we cannot determine for sure that there has been a write already
    // so generate a read even if l1_identifier has been written on
    // all branches flowing into this read
    guardt read_guard{false_exprt{}, guard_manager};

    a_s_r_entryt &a_s_read=read_in_atomic_section[ssa_l1];
    for(const auto &a_s_read_guard : a_s_read.second)
    {
      guardt g = a_s_read_guard; // copy
      g-=guard;
      if(g.is_true())
        // There has already been a read of l1_identifier within this atomic
        // section under the same guard, or a guard implied by the current one.
        return false;

      read_guard |= a_s_read_guard;
    }

    guardt cond = read_guard;
    if(!no_write.op().is_false())
      cond |= guardt{no_write.op(), guard_manager};

    // It is safe to perform constant propagation in case we have read or
    // written this object within the atomic section. We must actually do this,
    // because goto_state::apply_condition may have placed the latest value in
    // the propagation map without recording an assignment.
    auto p_it = propagation.find(ssa_l1.get_identifier());
    const exprt l2_true_case =
      p_it.has_value() ? *p_it : set_indices<L2>(ssa_l1, ns).get();

    if(!cond.is_true())
      level2.increase_generation(l1_identifier, ssa_l1, fresh_l2_name_provider);

    if(a_s_read.second.empty())
      a_s_read.first = level2.latest_index(l1_identifier);

    const renamedt<ssa_exprt, L2> l2_false_case = set_indices<L2>(ssa_l1, ns);

    exprt tmp;
    if(cond.is_false())
      tmp = l2_false_case.get();
    else if(cond.is_true())
      tmp = l2_true_case;
    else
      tmp = if_exprt{cond.as_expr(), l2_true_case, l2_false_case.get()};

    record_events.push(false);
    ssa_exprt ssa_l2 = assignment(std::move(ssa_l1), tmp, ns, true, true).get();
    record_events.pop();

    symex_target->assignment(
      guard_as_expr,
      ssa_l2,
      ssa_l2,
      ssa_l2.get_original_expr(),
      tmp,
      source,
      symex_targett::assignment_typet::PHI);

    INVARIANT(!check_renaming(ssa_l2), "expr should be renamed to L2");
    expr = std::move(ssa_l2);

    a_s_read.second.push_back(guard);
    if(!no_write.op().is_false())
      a_s_read.second.back().add(no_write);

    return true;
  }

  // No event and no fresh index, but avoid constant propagation
  if(!record_events.top())
  {
    expr = set_indices<L2>(std::move(ssa_l1), ns).get();
    return true;
  }

  // produce a fresh L2 name
  level2.increase_generation(l1_identifier, ssa_l1, fresh_l2_name_provider);
  expr = set_indices<L2>(std::move(ssa_l1), ns).get();

  // and record that
  INVARIANT_STRUCTURED(
    symex_target!=nullptr, nullptr_exceptiont, "symex_target is null");
  symex_target->shared_read(guard_as_expr, expr, atomic_section_id, source);

  return true;
}

goto_symex_statet::write_is_shared_resultt goto_symex_statet::write_is_shared(
  const ssa_exprt &expr,
  const namespacet &ns) const
{
  if(!record_events.top())
    return write_is_shared_resultt::NOT_SHARED;

  PRECONDITION(dirty != nullptr);
  const irep_idt &obj_identifier = expr.get_object_name();
  if(
    obj_identifier == guard_identifier() ||
    (!ns.lookup(obj_identifier).is_shared() && !(*dirty)(obj_identifier)))
  {
    return write_is_shared_resultt::NOT_SHARED;
  }

  // only continue if an indivisible object is being accessed
  if(field_sensitivity.is_divisible(expr))
    return write_is_shared_resultt::NOT_SHARED;

  if(atomic_section_id != 0)
    return write_is_shared_resultt::IN_ATOMIC_SECTION;

  return write_is_shared_resultt::SHARED;
}

/// thread encoding
/// \return true if \p expr is shared between threads
bool goto_symex_statet::l2_thread_write_encoding(
  const ssa_exprt &expr,
  const namespacet &ns)
{
  switch(write_is_shared(expr, ns))
  {
  case write_is_shared_resultt::NOT_SHARED:
    return false;
  case write_is_shared_resultt::IN_ATOMIC_SECTION:
  {
    written_in_atomic_section[remove_level_2(expr)].push_back(guard);
    return false;
  }
  case write_is_shared_resultt::SHARED:
    break;
  }

  // record a shared write
  symex_target->shared_write(
    guard.as_expr(),
    expr,
    atomic_section_id,
    source);

  // do we have threads?
  return threads.size() > 1;
}

template <levelt level>
void goto_symex_statet::rename_address(exprt &expr, const namespacet &ns)
{
  if(is_ssa_expr(expr))
  {
    ssa_exprt &ssa=to_ssa_expr(expr);

    // only do L1!
    ssa = set_indices<L1>(std::move(ssa), ns).get();

    rename<level>(expr.type(), ssa.get_identifier(), ns);
    ssa.update_type();
  }
  else if(expr.id()==ID_symbol)
  {
    expr=ssa_exprt(expr);
    rename_address<level>(expr, ns);
  }
  else
  {
    if(expr.id()==ID_index)
    {
      index_exprt &index_expr=to_index_expr(expr);

      rename_address<level>(index_expr.array(), ns);
      PRECONDITION(index_expr.array().type().id() == ID_array);
      expr.type() = to_array_type(index_expr.array().type()).element_type();

      // the index is not an address
      index_expr.index() =
        rename<level>(std::move(index_expr.index()), ns).get();
    }
    else if(expr.id()==ID_if)
    {
      // the condition is not an address
      if_exprt &if_expr=to_if_expr(expr);
      if_expr.cond() = rename<level>(std::move(if_expr.cond()), ns).get();
      rename_address<level>(if_expr.true_case(), ns);
      rename_address<level>(if_expr.false_case(), ns);

      if_expr.type()=if_expr.true_case().type();
    }
    else if(expr.id()==ID_member)
    {
      member_exprt &member_expr=to_member_expr(expr);

      rename_address<level>(member_expr.struct_op(), ns);

      // type might not have been renamed in case of nesting of
      // structs and pointers/arrays
      if(
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
        rename<level>(expr.type(), irep_idt(), ns);
    }
    else
    {
      // this could go wrong, but we would have to re-typecheck ...
      rename<level>(expr.type(), irep_idt(), ns);

      // do this recursively; we assume here
      // that all the operands are addresses
      Forall_operands(it, expr)
        rename_address<level>(*it, ns);
    }
  }
}

/// Return true if, and only if, the \p type or one of its subtypes requires SSA
/// renaming. Renaming is necessary when symbol expressions occur within the
/// type, which is the case for arrays of non-constant size.
static bool requires_renaming(const typet &type, const namespacet &ns)
{
  if(type.id() == ID_array)
  {
    const auto &array_type = to_array_type(type);
    return requires_renaming(array_type.element_type(), ns) ||
           !array_type.size().is_constant();
  }
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    const struct_union_typet &s_u_type = to_struct_union_type(type);
    const struct_union_typet::componentst &components = s_u_type.components();

    for(auto &component : components)
    {
      // be careful, or it might get cyclic
      if(component.type().id() == ID_array)
      {
        if(!to_array_type(component.type()).size().is_constant())
          return true;
      }
      else if(
        component.type().id() != ID_pointer &&
        requires_renaming(component.type(), ns))
      {
        return true;
      }
    }

    return false;
  }
  else if(type.id() == ID_pointer)
  {
    return requires_renaming(to_pointer_type(type).base_type(), ns);
  }
  else if(type.id() == ID_union_tag)
  {
    const symbolt &symbol = ns.lookup(to_union_tag_type(type));
    return requires_renaming(symbol.type, ns);
  }
  else if(type.id() == ID_struct_tag)
  {
    const symbolt &symbol = ns.lookup(to_struct_tag_type(type));
    return requires_renaming(symbol.type, ns);
  }

  return false;
}

template <levelt level>
void goto_symex_statet::rename(
  typet &type,
  const irep_idt &l1_identifier,
  const namespacet &ns)
{
  // check whether there are symbol expressions in the type; if not, there
  // is no need to expand the struct/union tags in the type
  if(!requires_renaming(type, ns))
    return; // no action

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

  // expand struct and union tag types
  type = ns.follow(type);

  if(type.id()==ID_array)
  {
    auto &array_type = to_array_type(type);
    rename<level>(array_type.element_type(), irep_idt(), ns);
    array_type.size() = rename<level>(std::move(array_type.size()), ns).get();
  }
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    struct_union_typet &s_u_type=to_struct_union_type(type);
    struct_union_typet::componentst &components=s_u_type.components();

    for(auto &component : components)
    {
      // be careful, or it might get cyclic
      if(component.type().id() == ID_array)
      {
        auto &array_type = to_array_type(component.type());
        array_type.size() =
          rename<level>(std::move(array_type.size()), ns).get();
      }
      else if(component.type().id() != ID_pointer)
        rename<level>(component.type(), irep_idt(), ns);
    }
  }
  else if(type.id()==ID_pointer)
  {
    rename<level>(to_pointer_type(type).base_type(), irep_idt(), ns);
  }

  if(level==L2 &&
     !l1_identifier.empty())
    l1_type_entry.first->second=type;
}

static void get_l1_name(exprt &expr)
{
  // do not reset the type !

  if(is_ssa_expr(expr))
    to_ssa_expr(expr).remove_level_2();
  else
    Forall_operands(it, expr)
      get_l1_name(*it);
}

/// Dumps the current state of symex, printing the function name and location
/// number for each stack frame in the currently active thread.
/// This is for use from the debugger or in debug code; please don't delete it
/// just because it isn't called at present.
/// \param out: stream to write to
void goto_symex_statet::print_backtrace(std::ostream &out) const
{
  if(threads[source.thread_nr].call_stack.empty())
  {
    out << "No stack!\n";
    return;
  }

  out << source.function_id << " " << source.pc->location_number << "\n";

  for(auto stackit = threads[source.thread_nr].call_stack.rbegin(),
           stackend = threads[source.thread_nr].call_stack.rend();
      stackit != stackend;
      ++stackit)
  {
    const auto &frame = *stackit;
    out << frame.calling_location.function_id << " "
        << frame.calling_location.pc->location_number << "\n";
  }
}

ssa_exprt goto_symex_statet::add_object(
  const symbol_exprt &expr,
  std::function<std::size_t(const irep_idt &)> index_generator,
  const namespacet &ns)
{
  framet &frame = call_stack().top();

  const renamedt<ssa_exprt, L0> renamed = rename_ssa<L0>(ssa_exprt{expr}, ns);
  const irep_idt l0_name = renamed.get_identifier();
  const std::size_t l1_index = index_generator(l0_name);

  if(const auto old_value = level1.insert_or_replace(renamed, l1_index))
  {
    // save old L1 name
    if(!frame.old_level1.has(renamed))
      frame.old_level1.insert(renamed, old_value->second);
  }

  const ssa_exprt ssa = rename_ssa<L1>(renamed.get(), ns).get();
  const bool inserted = frame.local_objects.insert(ssa.get_identifier()).second;
  INVARIANT(inserted, "l1_name expected to be unique by construction");

  return ssa;
}

ssa_exprt goto_symex_statet::declare(ssa_exprt ssa, const namespacet &ns)
{
  const irep_idt &l1_identifier = ssa.get_identifier();

  // rename type to L2
  rename(ssa.type(), l1_identifier, ns);
  ssa.update_type();

  // in case of pointers, put something into the value set
  if(ssa.type().id() == ID_pointer)
  {
    exprt rhs;
    if(
      auto failed =
        get_failed_symbol(to_symbol_expr(ssa.get_original_expr()), ns))
      rhs = address_of_exprt(*failed, to_pointer_type(ssa.type()));
    else
      rhs = exprt(ID_invalid);

    exprt l1_rhs = rename<L1>(std::move(rhs), ns).get();
    value_set.assign(ssa, l1_rhs, ns, true, false);
  }

  // L2 renaming
  const exprt fields = field_sensitivity.get_fields(ns, *this, ssa);
  for(const auto &l1_symbol : find_symbols(fields))
  {
    const ssa_exprt &field_ssa = to_ssa_expr(l1_symbol);
    const std::size_t field_generation = level2.increase_generation(
      l1_symbol.get_identifier(), field_ssa, fresh_l2_name_provider);
    CHECK_RETURN(field_generation == 1);
  }

  record_events.push(false);
  exprt expr_l2 = rename(std::move(ssa), ns).get();
  INVARIANT(
    is_ssa_expr(expr_l2),
    "symbol to declare should not be replaced by constant propagation");
  ssa = to_ssa_expr(expr_l2);
  record_events.pop();

  return ssa;
}
