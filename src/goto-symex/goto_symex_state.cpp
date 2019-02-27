/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Symbolic Execution

#include "goto_symex_state.h"

#include <cstdlib>
#include <iostream>

#include <util/as_const.h>
#include <util/base_exceptions.h>
#include <util/exception_utils.h>
#include <util/expr_util.h>
#include <util/format.h>
#include <util/format_expr.h>
#include <util/invariant.h>
#include <util/pointer_predicates.h>
#include <util/prefix.h>
#include <util/std_expr.h>

#include <analyses/dirty.h>

static void get_l1_name(exprt &expr);

goto_symex_statet::goto_symex_statet(
  const symex_targett::sourcet &_source,
  guard_managert &manager)
  : goto_statet(_source, manager),
    guard_manager(manager),
    symex_target(nullptr),
    record_events(true),
    dirty()
{
  threads.emplace_back(guard_manager);
  call_stack().new_frame(source);
}

goto_symex_statet::~goto_symex_statet()=default;

/// write to a variable
static bool check_renaming(const exprt &expr);

static bool check_renaming(const typet &type)
{
  if(type.id()==ID_array)
    return check_renaming(to_array_type(type).size());
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    for(const auto &c : to_struct_union_type(type).components())
      if(check_renaming(c.type()))
        return true;
  }
  else if(type.has_subtype())
    return check_renaming(to_type_with_subtype(type).subtype());

  return false;
}

static bool check_renaming_l1(const exprt &expr)
{
  if(check_renaming(expr.type()))
    return true;

  if(expr.id()==ID_symbol)
  {
    const auto &type = expr.type();
    if(!expr.get_bool(ID_C_SSA_symbol))
      return type.id() != ID_code && type.id() != ID_mathematical_function;
    if(!to_ssa_expr(expr).get_level_2().empty())
      return true;
    if(to_ssa_expr(expr).get_original_expr().type() != type)
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

  if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_symbol)
  {
    return check_renaming_l1(to_address_of_expr(expr).object());
  }
  else if(
    expr.id() == ID_address_of &&
    to_address_of_expr(expr).object().id() == ID_index)
  {
    const auto index_expr = to_index_expr(to_address_of_expr(expr).object());
    return check_renaming_l1(index_expr.array()) ||
           check_renaming(index_expr.index());
  }
  else if(expr.id()==ID_symbol)
  {
    const auto &type = expr.type();
    if(!expr.get_bool(ID_C_SSA_symbol))
      return type.id() != ID_code && type.id() != ID_mathematical_function;
    if(to_ssa_expr(expr).get_level_2().empty())
      return true;
    if(to_ssa_expr(expr).get_original_expr().type() != type)
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

class goto_symex_is_constantt : public is_constantt
{
protected:
  bool is_constant(const exprt &expr) const override
  {
    if(expr.id() == ID_mult)
    {
      // propagate stuff with sizeof in it
      forall_operands(it, expr)
      {
        if(it->find(ID_C_c_sizeof_type).is_not_nil())
          return true;
        else if(!is_constant(*it))
          return false;
      }

      return true;
    }
    else if(expr.id() == ID_with)
    {
      // this is bad
      /*
      forall_operands(it, expr)
      if(!is_constant(expr.op0()))
      return false;

      return true;
      */
      return false;
    }

    return is_constantt::is_constant(expr);
  }
};

template <>
renamedt<ssa_exprt, L0>
goto_symex_statet::set_indices<L0>(ssa_exprt ssa_expr, const namespacet &ns)
{
  return level0(std::move(ssa_expr), ns, source.thread_nr);
}

template <>
renamedt<ssa_exprt, L1>
goto_symex_statet::set_indices<L1>(ssa_exprt ssa_expr, const namespacet &ns)
{
  return level1(level0(std::move(ssa_expr), ns, source.thread_nr));
}

template <>
renamedt<ssa_exprt, L2>
goto_symex_statet::set_indices<L2>(ssa_exprt ssa_expr, const namespacet &ns)
{
  return level2(level1(level0(std::move(ssa_expr), ns, source.thread_nr)));
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
  lhs = rename_ssa<L1>(std::move(lhs), ns);
  irep_idt l1_identifier=lhs.get_identifier();

  // the type might need renaming
  rename<L2>(lhs.type(), l1_identifier, ns);
  lhs.update_type();
  if(run_validation_checks)
  {
    DATA_INVARIANT(!check_renaming_l1(lhs), "lhs renaming failed on l1");
  }

#if 0
  PRECONDITION(l1_identifier != get_original_name(l1_identifier)
      || l1_identifier == guard_identifier()
      || ns.lookup(l1_identifier).is_shared()
      || has_prefix(id2string(l1_identifier), "symex::invalid_object")
      || has_prefix(id2string(l1_identifier), SYMEX_DYNAMIC_PREFIX "dynamic_object"));
#endif

  // do the l2 renaming
  const auto level2_it =
    level2.current_names.emplace(l1_identifier, std::make_pair(lhs, 0)).first;
  symex_renaming_levelt::increase_counter(level2_it);
  lhs = set_indices<L2>(std::move(lhs), ns).get();

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

  // for value propagation -- the RHS is L2

  if(!is_shared && record_value && goto_symex_is_constantt()(rhs))
    propagation[l1_identifier] = rhs;
  else
    propagation.erase(l1_identifier);

  {
    // update value sets
    exprt l1_rhs(rhs);
    get_l1_name(l1_rhs);

    ssa_exprt l1_lhs(lhs);
    l1_lhs.remove_level_2();

    if(run_validation_checks)
    {
      DATA_INVARIANT(!check_renaming_l1(l1_lhs), "lhs renaming failed on l1");
      DATA_INVARIANT(!check_renaming_l1(l1_rhs), "rhs renaming failed on l1");
    }

    value_set.assign(l1_lhs, l1_rhs, ns, rhs_is_simplified, is_shared);
  }

  #if 0
  std::cout << "Assigning " << l1_identifier << '\n';
  value_set.output(ns, std::cout);
  std::cout << "**********************\n";
  #endif
}

template <levelt level>
ssa_exprt goto_symex_statet::rename_ssa(ssa_exprt ssa, const namespacet &ns)
{
  static_assert(
    level == L0 || level == L1,
    "rename_ssa can only be used for levels L0 and L1");
  ssa = set_indices<level>(std::move(ssa), ns).get();
  rename<level>(ssa.type(), ssa.get_identifier(), ns);
  ssa.update_type();
  return ssa;
}

// explicitly instantiate templates
template ssa_exprt
goto_symex_statet::rename_ssa<L0>(ssa_exprt ssa, const namespacet &ns);
template ssa_exprt
goto_symex_statet::rename_ssa<L1>(ssa_exprt ssa, const namespacet &ns);

template <levelt level>
exprt goto_symex_statet::rename(exprt expr, const namespacet &ns)
{
  // rename all the symbols with their last known value

  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
  {
    ssa_exprt &ssa=to_ssa_expr(expr);

    if(level == L0)
    {
      ssa = rename_ssa<L0>(std::move(ssa), ns);
    }
    else if(level == L1)
    {
      ssa = rename_ssa<L1>(std::move(ssa), ns);
    }
    else if(level==L2)
    {
      ssa = set_indices<L1>(std::move(ssa), ns).get();
      if(
        auto renamed_type =
          rename_type<level>(expr.type(), ssa.get_identifier(), ns))
      {
        ssa.type() = std::move(*renamed_type);
        ssa.update_type();
      }

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
        auto p_it = propagation.find(ssa.get_identifier());

        if(p_it != propagation.end())
          expr=p_it->second; // already L2
        else
          ssa = set_indices<L2>(std::move(ssa), ns).get();
      }
    }
  }
  else if(expr.id()==ID_symbol)
  {
    // we never rename function symbols
    if(
      expr.type().id() == ID_code ||
      expr.type().id() == ID_mathematical_function)
    {
      if(
        auto renamed_type = rename_type<level>(
          expr.type(), to_symbol_expr(expr).get_identifier(), ns))
      {
        expr.type() = std::move(*renamed_type);
      }
    }
    else
      expr = rename<level>(ssa_exprt{expr}, ns);
  }
  else if(expr.id()==ID_address_of)
  {
    auto &address_of_expr = to_address_of_expr(expr);
    auto renamed_object = rename_address<level>(address_of_expr.object(), ns);

    if(renamed_object.has_value())
      expr = address_of_exprt{std::move(*renamed_object)};
  }
  else
  {
    if(auto renamed_type = rename_type<level>(expr.type(), irep_idt(), ns))
    {
      expr.type() = std::move(*renamed_type);
    }

    // do this recursively
    Forall_operands(it, expr)
      *it = rename<level>(std::move(*it), ns);

    const exprt &c_expr = as_const(expr);
    INVARIANT(
      (expr.id() != ID_with ||
       c_expr.type() == to_with_expr(c_expr).old().type()) &&
        (expr.id() != ID_if ||
         (c_expr.type() == to_if_expr(c_expr).true_case().type() &&
          c_expr.type() == to_if_expr(c_expr).false_case().type())),
      "Type of renamed expr should be the same as operands for with_exprt and "
      "if_exprt");
  }
  return expr;
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
    obj_identifier == guard_identifier() ||
    (!ns.lookup(obj_identifier).is_shared() && !(dirty)(obj_identifier)))
  {
    return false;
  }

  ssa_exprt ssa_l1=expr;
  ssa_l1.remove_level_2();
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
          // there has already been a write to l1_identifier within
          // this atomic section under the same guard, or a guard
          // that implies the current one
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
        // there has already been a read l1_identifier within
        // this atomic section under the same guard, or a guard
        // that implies the current one
        return false;

      read_guard |= a_s_read_guard;
    }

    guardt cond = read_guard;
    if(!no_write.op().is_false())
      cond |= guardt{no_write.op(), guard_manager};

    const renamedt<ssa_exprt, L2> l2_true_case = set_indices<L2>(ssa_l1, ns);

    if(a_s_read.second.empty())
    {
      auto level2_it =
        level2.current_names.emplace(l1_identifier, std::make_pair(ssa_l1, 0))
          .first;
      symex_renaming_levelt::increase_counter(level2_it);
      a_s_read.first=level2.current_count(l1_identifier);
    }
    const renamedt<ssa_exprt, L2> l2_false_case = set_indices<L2>(ssa_l1, ns);

    exprt tmp;
    if(cond.is_false())
      tmp = l2_false_case.get();
    else
      tmp = if_exprt{cond.as_expr(), l2_true_case.get(), l2_false_case.get()};

    const bool record_events_bak=record_events;
    record_events=false;
    assignment(ssa_l1, tmp, ns, true, true);
    record_events=record_events_bak;

    symex_target->assignment(
      guard_as_expr,
      ssa_l1,
      ssa_l1,
      ssa_l1.get_original_expr(),
      tmp,
      source,
      symex_targett::assignment_typet::PHI);

    expr = set_indices<L2>(std::move(ssa_l1), ns).get();

    a_s_read.second.push_back(guard);
    if(!no_write.op().is_false())
      a_s_read.second.back().add(no_write);

    return true;
  }

  const auto level2_it =
    level2.current_names.emplace(l1_identifier, std::make_pair(ssa_l1, 0))
      .first;

  // No event and no fresh index, but avoid constant propagation
  if(!record_events)
  {
    expr = set_indices<L2>(std::move(ssa_l1), ns).get();
    return true;
  }

  // produce a fresh L2 name
  symex_renaming_levelt::increase_counter(level2_it);
  expr = set_indices<L2>(std::move(ssa_l1), ns).get();

  // and record that
  INVARIANT_STRUCTURED(
    symex_target!=nullptr, nullptr_exceptiont, "symex_target is null");
  symex_target->shared_read(guard_as_expr, expr, atomic_section_id, source);

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
    obj_identifier == guard_identifier() ||
    (!ns.lookup(obj_identifier).is_shared() && !(dirty)(obj_identifier)))
  {
    return false; // not shared
  }

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

template <levelt level>
optionalt<exprt>
goto_symex_statet::rename_address(const exprt &expr, const namespacet &ns)
{
  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
  {
    ssa_exprt ssa = to_ssa_expr(expr);

    // only do L1!
    ssa = set_indices<L1>(std::move(ssa), ns).get();

    if(
      auto renamed_type =
        rename_type<level>(expr.type(), ssa.get_identifier(), ns))
    {
      ssa.type() = std::move(*renamed_type);
      ssa.update_type();
    }

    return std::move(ssa);
  }
  else if(expr.id()==ID_symbol)
  {
    ssa_exprt ssa{expr};
    if(auto renamed = rename_address<level>(ssa, ns))
      return renamed;
    else
      return std::move(ssa);
  }
  else if(expr.id() == ID_index)
  {
    const index_exprt &index_expr = to_index_expr(expr);

    auto renamed_array = rename_address<level>(index_expr.array(), ns);

    // the index is not an address
    auto renamed_index = rename<level>(index_expr.index(), ns);

    if(renamed_array.has_value() || renamed_index != index_expr.index())
    {
      index_exprt result = index_expr;

      if(renamed_array.has_value())
      {
        result.array() = std::move(*renamed_array);
        result.type() = to_array_type(result.array().type()).subtype();
      }

      if(renamed_index != index_expr.index())
        result.index() = std::move(renamed_index);

      return std::move(result);
    }
    else
      return {};
  }
  else if(expr.id() == ID_if)
  {
    // the condition is not an address
    const if_exprt &if_expr = to_if_expr(expr);
    auto renamed_cond = rename<level>(if_expr.cond(), ns);
    auto renamed_true = rename_address<level>(if_expr.true_case(), ns);
    auto renamed_false = rename_address<level>(if_expr.false_case(), ns);

    if(
      renamed_cond != if_expr.cond() || renamed_true.has_value() ||
      renamed_false.has_value())
    {
      if_exprt result = if_expr;

      if(renamed_cond != if_expr.cond())
        result.cond() = std::move(renamed_cond);

      if(renamed_true.has_value())
      {
        result.true_case() = std::move(*renamed_true);
        result.type() = result.true_case().type();
      }

      if(renamed_false.has_value())
        result.false_case() = std::move(*renamed_false);

      return std::move(result);
    }
    else
      return {};
  }
  else if(expr.id() == ID_member)
  {
    const member_exprt &member_expr = to_member_expr(expr);

    auto renamed_struct_op = rename_address<level>(member_expr.struct_op(), ns);

    // type might not have been renamed in case of nesting of
    // structs and pointers/arrays
    optionalt<typet> renamed_type;
    if(
      renamed_struct_op.has_value() &&
      renamed_struct_op->type().id() != ID_struct_tag &&
      renamed_struct_op->type().id() != ID_union_tag)
    {
      const struct_union_typet &su_type =
        to_struct_union_type(renamed_struct_op->type());
      const struct_union_typet::componentt &comp =
        su_type.get_component(member_expr.get_component_name());
      DATA_INVARIANT(comp.is_not_nil(), "component should exist");
      renamed_type = comp.type();
    }
    else
      renamed_type = rename_type<level>(expr.type(), irep_idt(), ns);

    if(renamed_struct_op.has_value() || renamed_type.has_value())
    {
      member_exprt result = member_expr;

      if(renamed_struct_op.has_value())
        result.struct_op() = std::move(*renamed_struct_op);

      if(renamed_type.has_value())
        result.type() = std::move(*renamed_type);

      return std::move(result);
    }
    else
      return {};
  }
  else
  {
    optionalt<exprt> result;

    // this could go wrong, but we would have to re-typecheck ...
    if(auto renamed_type = rename_type<level>(expr.type(), irep_idt(), ns))
    {
      result = expr;
      result->type() = std::move(*renamed_type);
    }

    // do this recursively; we assume here
    // that all the operands are addresses
    optionalt<exprt::operandst> result_operands;
    std::size_t op_index = 0;

    for(auto &op : expr.operands())
    {
      if(auto renamed_op = rename_address<level>(op, ns))
      {
        if(!result_operands.has_value())
          result_operands = expr.operands();

        (*result_operands)[op_index] = std::move(*renamed_op);
      }
      ++op_index;
    }

    if(result_operands.has_value())
    {
      if(!result.has_value())
        result = expr;

      result->operands() = std::move(*result_operands);
    }

    return result;
  }
}

template <levelt level>
void goto_symex_statet::rename(
  typet &type,
  const irep_idt &l1_identifier,
  const namespacet &ns)
{
  if(auto renamed = rename_type<level>(type, l1_identifier, ns))
    type = std::move(*renamed);
}

// explicitly instantiate templates
/// \cond
template void goto_symex_statet::rename<L2>(
  typet &type,
  const irep_idt &l1_identifier,
  const namespacet &ns);
/// \endcond

template <levelt level>
optionalt<typet> goto_symex_statet::rename_type(
  const typet &type,
  const irep_idt &l1_identifier,
  const namespacet &ns)
{
  // rename all the symbols with their last known value
  // to the given level

  if(level==L2 &&
     !l1_identifier.empty())
  {
    auto l1_type_entry = l1_types.find(l1_identifier);

    if(l1_type_entry != l1_types.end())
    {
      // do not change a complete array type to an incomplete one

      const typet &type_prev = l1_type_entry->second;

      if(type.id()!=ID_array ||
         type_prev.id()!=ID_array ||
         to_array_type(type).is_incomplete() ||
         to_array_type(type_prev).is_complete())
      {
        return l1_type_entry->second;
      }
    }
  }

  optionalt<typet> result;

  if(type.id()==ID_array)
  {
    auto &array_type = to_array_type(type);
    auto renamed_subtype =
      rename_type<level>(array_type.subtype(), irep_idt(), ns);
    auto renamed_size = rename<level>(array_type.size(), ns);

    if(renamed_subtype.has_value() || renamed_size != array_type.size())
    {
      array_typet result_type = array_type;

      if(renamed_subtype.has_value())
        result_type.subtype() = std::move(*renamed_subtype);

      if(renamed_size != array_type.size())
        result_type.size() = std::move(renamed_size);

      result = std::move(result_type);
    }
  }
  else if(type.id() == ID_struct || type.id() == ID_union)
  {
    struct_union_typet s_u_type = to_struct_union_type(type);
    bool modified = false;

    struct_union_typet::componentst::iterator comp_it =
      s_u_type.components().begin();
    for(auto &component : to_struct_union_type(type).components())
    {
      // be careful, or it might get cyclic
      if(component.type().id() == ID_array)
      {
        auto &array_type = to_array_type(component.type());
        auto renamed_expr = rename<level>(array_type.size(), ns);
        if(renamed_expr != array_type.size())
        {
          to_array_type(comp_it->type()).size() = std::move(renamed_expr);
          modified = true;
        }
      }
      else if(component.type().id() != ID_pointer)
      {
        if(
          auto renamed_type =
            rename_type<level>(component.type(), irep_idt(), ns))
        {
          comp_it->type() = std::move(*renamed_type);
          modified = true;
        }
      }

      ++comp_it;
    }

    if(modified)
      result = std::move(s_u_type);
  }
  else if(type.id()==ID_pointer)
  {
    auto renamed_subtype =
      rename_type<level>(to_pointer_type(type).subtype(), irep_idt(), ns);
    if(renamed_subtype.has_value())
    {
      result = pointer_typet{std::move(*renamed_subtype),
                             to_pointer_type(type).get_width()};
    }
  }
  else if(type.id() == ID_struct_tag || type.id() == ID_union_tag)
  {
    result = rename_type<level>(ns.follow(type), l1_identifier, ns);
  }

  if(level == L2 && !l1_identifier.empty() && result.has_value())
    l1_types.emplace(l1_identifier, *result);

  return result;
}

static void get_l1_name(exprt &expr)
{
  // do not reset the type !

  if(expr.id()==ID_symbol &&
     expr.get_bool(ID_C_SSA_symbol))
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

  ssa_exprt ssa = rename_ssa<L0>(ssa_exprt{expr}, ns);
  const irep_idt l0_name = ssa.get_identifier();
  const std::size_t l1_index = index_generator(l0_name);

  // save old L1 name, if any
  auto existing_or_new_entry = level1.current_names.emplace(
    std::piecewise_construct,
    std::forward_as_tuple(l0_name),
    std::forward_as_tuple(ssa, l1_index));

  if(!existing_or_new_entry.second)
  {
    frame.old_level1.emplace(l0_name, existing_or_new_entry.first->second);
    existing_or_new_entry.first->second = std::make_pair(ssa, l1_index);
  }

  ssa = rename_ssa<L1>(std::move(ssa), ns);
  const bool inserted = frame.local_objects.insert(ssa.get_identifier()).second;
  INVARIANT(inserted, "l1_name expected to be unique by construction");

  return ssa;
}
