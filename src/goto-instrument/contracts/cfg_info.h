/*******************************************************************\

Module: CFG-based information for assigns clause checking simplification

Author: Remi Delmas

Date: June 2022

\*******************************************************************/

/// \file
/// Classes providing CFG-based information about symbols to guide
/// simplifications in function and loop assigns clause checking

#ifndef CPROVER_GOTO_INSTRUMENT_CONTRACTS_CFG_INFO_H
#define CPROVER_GOTO_INSTRUMENT_CONTRACTS_CFG_INFO_H

#include <ansi-c/goto-conversion/goto_convert_class.h>

#include <util/byte_operators.h>
#include <util/expr_cast.h>
#include <util/find_symbols.h>
#include <util/message.h>

#include <goto-programs/goto_model.h>

#include <analyses/dirty.h>
#include <analyses/locals.h>
#include <goto-instrument/havoc_utils.h>
#include <goto-instrument/loop_utils.h>

#include <set>
#include <vector>

/// Stores information about a goto function computed from its CFG.
///
/// The methods of this class provide information about identifiers
/// to allow simplifying assigns clause checking assertions.
class cfg_infot
{
public:
  /// Returns true iff `ident` is locally declared.
  virtual bool is_local(const irep_idt &ident) const = 0;

  /// Returns true iff the given `ident` is either non-locally declared
  /// or is locally-declared but dirty.
  virtual bool is_not_local_or_dirty_local(const irep_idt &ident) const = 0;

  /// Returns true iff `expr` is an access to a locally declared symbol
  /// and does not contain `dereference` or `address_of` operations.
  bool is_local_composite_access(const exprt &expr) const
  {
    // case-splitting on the lhs structure copied from symex_assignt::assign_rec
    if(expr.id() == ID_symbol)
    {
      return is_local(to_symbol_expr(expr).get_identifier());
    }
    else if(expr.id() == ID_index)
    {
      return is_local_composite_access(to_index_expr(expr).array());
    }
    else if(expr.id() == ID_member)
    {
      const typet &type = to_member_expr(expr).struct_op().type();
      if(
        type.id() == ID_struct || type.id() == ID_struct_tag ||
        type.id() == ID_union || type.id() == ID_union_tag)
      {
        return is_local_composite_access(to_member_expr(expr).compound());
      }
      else
      {
        throw unsupported_operation_exceptiont(
          "is_local_composite_access: unexpected assignment to member of '" +
          type.id_string() + "'");
      }
    }
    else if(expr.id() == ID_if)
    {
      return is_local_composite_access(to_if_expr(expr).true_case()) &&
             is_local_composite_access(to_if_expr(expr).false_case());
    }
    else if(expr.id() == ID_typecast)
    {
      return is_local_composite_access(to_typecast_expr(expr).op());
    }
    else if(
      expr.id() == ID_byte_extract_little_endian ||
      expr.id() == ID_byte_extract_big_endian)
    {
      return is_local_composite_access(to_byte_extract_expr(expr).op());
    }
    else if(expr.id() == ID_complex_real)
    {
      return is_local_composite_access(to_complex_real_expr(expr).op());
    }
    else if(expr.id() == ID_complex_imag)
    {
      return is_local_composite_access(to_complex_imag_expr(expr).op());
    }
    else
    {
      // matches ID_address_of, ID_dereference, etc.
      return false;
    }
  }
};

// For goto_functions
class function_cfg_infot : public cfg_infot
{
public:
  explicit function_cfg_infot(const goto_functiont &_goto_function)
    : is_dirty(_goto_function), locals(_goto_function)
  {
    parameters.insert(
      _goto_function.parameter_identifiers.begin(),
      _goto_function.parameter_identifiers.end());
  }

  /// Returns true iff `ident` is a local or parameter of the goto_function.
  bool is_local(const irep_idt &ident) const override
  {
    return locals.is_local(ident) ||
           (parameters.find(ident) != parameters.end());
  }

  /// Returns true iff the given `ident` is either not a goto_function local
  /// or is a local that is dirty.
  bool is_not_local_or_dirty_local(const irep_idt &ident) const override
  {
    return is_local(ident) ? is_dirty(ident) : true;
  }

private:
  const dirtyt is_dirty;
  const localst locals;
  std::unordered_set<irep_idt> parameters;
};

// For a loop in a goto_function
class loop_cfg_infot : public cfg_infot
{
public:
  loop_cfg_infot(goto_functiont &_goto_function, const loopt &loop)
    : is_dirty(_goto_function)
  {
    for(const auto &t : loop)
    {
      if(t->is_decl())
        locals.insert(t->decl_symbol().get_identifier());
    }
  }

  /// Returns true iff `ident` is a loop local.
  bool is_local(const irep_idt &ident) const override
  {
    return locals.find(ident) != locals.end();
  }

  /// Returns true iff the given `ident` is either not a loop local
  /// or is a loop local that is dirty.
  bool is_not_local_or_dirty_local(const irep_idt &ident) const override
  {
    if(is_local(ident))
      return is_dirty(ident);
    else
      return true;
  }

  void erase_locals(std::set<exprt> &exprs)
  {
    auto it = exprs.begin();
    while(it != exprs.end())
    {
      const std::unordered_set<irep_idt> symbols = find_symbol_identifiers(*it);

      if(
        std::find_if(symbols.begin(), symbols.end(), [this](const irep_idt &s) {
          return is_local(s);
        }) != symbols.end())
      {
        it = exprs.erase(it);
      }
      else
      {
        it++;
      }
    }
  }

private:
  const dirtyt is_dirty;
  std::unordered_set<irep_idt> locals;
};

/// For a goto program. locals and dirty locals are inferred directly from
/// the instruction sequence.
class goto_program_cfg_infot : public cfg_infot
{
public:
  explicit goto_program_cfg_infot(const goto_programt &goto_program)
  {
    // collect symbols declared in the insruction sequence as locals
    goto_program.get_decl_identifiers(locals);

    // collect dirty locals
    goto_functiont goto_function;
    goto_function.body.copy_from(goto_program);

    dirtyt is_dirty(goto_function);
    const auto &dirty_ids = is_dirty.get_dirty_ids();
    dirty.insert(dirty_ids.begin(), dirty_ids.end());
  }

  /// Returns true iff `ident` is a loop local.
  bool is_local(const irep_idt &ident) const override
  {
    return locals.find(ident) != locals.end();
  }

  /// Returns true iff the given `ident` is either not a loop local
  /// or is a loop local that is dirty.
  bool is_not_local_or_dirty_local(const irep_idt &ident) const override
  {
    if(is_local(ident))
      return dirty.find(ident) != dirty.end();
    else
      return true;
  }

protected:
  std::set<irep_idt> locals;
  std::set<irep_idt> dirty;
};

#endif
