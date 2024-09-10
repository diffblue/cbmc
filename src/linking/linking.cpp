/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Linking

#include "linking.h"
#include "linking_class.h"

#include <util/c_types.h>
#include <util/find_symbols.h>
#include <util/message.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>
#include <util/symbol_table_base.h>

#include <langapi/language_util.h>

#include "linking_diagnostics.h"

#include <deque>

static const typet &follow_tags_symbols(
  const namespacet &ns,
  const typet &type)
{
  if(type.id() == ID_c_enum_tag)
    return ns.follow_tag(to_c_enum_tag_type(type));
  else if(type.id()==ID_struct_tag)
    return ns.follow_tag(to_struct_tag_type(type));
  else if(type.id()==ID_union_tag)
    return ns.follow_tag(to_union_tag_type(type));
  else
    return type;
}

irep_idt
linkingt::rename(const symbol_table_baset &src_symbol_table, const irep_idt &id)
{
  unsigned cnt=0;

  while(true)
  {
    irep_idt new_identifier=
      id2string(id)+"$link"+std::to_string(++cnt);

    if(main_symbol_table.symbols.find(new_identifier)!=
       main_symbol_table.symbols.end())
      continue; // already in main symbol table

    if(!renamed_ids.insert(new_identifier).second)
      continue; // used this for renaming already

    if(src_symbol_table.symbols.find(new_identifier)!=
       src_symbol_table.symbols.end())
      continue; // used by some earlier linking call already

    return new_identifier;
  }
}

linkingt::renamingt linkingt::needs_renaming_non_type(
  const symbolt &old_symbol,
  const symbolt &new_symbol)
{
  // We first take care of file-local non-type symbols.
  // These are static functions, or static variables
  // inside static function bodies.
  if(new_symbol.is_file_local)
    return renamingt::RENAME_NEW;
  else if(old_symbol.is_file_local)
    return renamingt::RENAME_OLD;
  else
    return renamingt::NO_RENAMING;
}

void linkingt::duplicate_code_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  linking_diagnosticst diag{message_handler, ns};

  // Both are functions.
  if(old_symbol.type != new_symbol.type)
  {
    const code_typet &old_t=to_code_type(old_symbol.type);
    const code_typet &new_t=to_code_type(new_symbol.type);

    if(old_symbol.type.get_bool(ID_C_incomplete) && old_symbol.value.is_nil())
    {
      diag.warning(old_symbol, new_symbol, "implicit function declaration");

      old_symbol.type=new_symbol.type;
      old_symbol.location=new_symbol.location;
      old_symbol.is_weak=new_symbol.is_weak;
    }
    else if(
      new_symbol.type.get_bool(ID_C_incomplete) && new_symbol.value.is_nil())
    {
      diag.warning(
        old_symbol,
        new_symbol,
        "ignoring conflicting implicit function declaration");
    }
    // handle (incomplete) function prototypes
    else if(((old_t.parameters().empty() && old_t.has_ellipsis() &&
              old_symbol.value.is_nil()) ||
             (new_t.parameters().empty() && new_t.has_ellipsis() &&
              new_symbol.value.is_nil())))
    {
      if(old_t.parameters().empty() &&
         old_t.has_ellipsis() &&
         old_symbol.value.is_nil())
      {
        old_symbol.type=new_symbol.type;
        old_symbol.location=new_symbol.location;
        old_symbol.is_weak=new_symbol.is_weak;
      }
    }
    // replace weak symbols
    else if(old_symbol.is_weak)
    {
      if(new_symbol.value.is_nil())
      {
        diag.warning(
          old_symbol,
          new_symbol,
          "function declaration conflicts with with weak definition");
      }
      else
        old_symbol.value.make_nil();
    }
    else if(new_symbol.is_weak)
    {
      if(new_symbol.value.is_nil() ||
         old_symbol.value.is_not_nil())
      {
        new_symbol.value.make_nil();

        diag.warning(
          old_symbol,
          new_symbol,
          "ignoring conflicting weak function declaration");
      }
    }
    // aliasing may alter the type
    else if((new_symbol.is_macro &&
             new_symbol.value.is_not_nil() &&
             old_symbol.value.is_nil()) ||
            (old_symbol.is_macro &&
             old_symbol.value.is_not_nil() &&
             new_symbol.value.is_nil()))
    {
      diag.warning(
        old_symbol,
        new_symbol,
        "ignoring conflicting function alias declaration");
    }
    // conflicting declarations without a definition, matching return
    // types
    else if(old_symbol.value.is_nil() && new_symbol.value.is_nil())
    {
      diag.warning(
        old_symbol, new_symbol, "ignoring conflicting function declarations");

      if(old_t.parameters().size()<new_t.parameters().size())
      {
        old_symbol.type=new_symbol.type;
        old_symbol.location=new_symbol.location;
        old_symbol.is_weak=new_symbol.is_weak;
      }
    }
    // mismatch on number of parameters is definitively an error
    else if((old_t.parameters().size()<new_t.parameters().size() &&
             new_symbol.value.is_not_nil() &&
             !old_t.has_ellipsis()) ||
            (old_t.parameters().size()>new_t.parameters().size() &&
             old_symbol.value.is_not_nil() &&
             !new_t.has_ellipsis()))
    {
      diag.error(
        old_symbol,
        new_symbol,
        "conflicting parameter counts of function declarations");

      // error logged, continue typechecking other symbols
      return;
    }
    else
    {
      // the number of parameters matches, collect all the conflicts
      // and see whether they can be cured
      std::string warn_msg;
      bool replace=false;
      typedef std::deque<std::pair<typet, typet> > conflictst;
      conflictst conflicts;

      if(old_t.return_type() != new_t.return_type())
      {
        diag.warning(old_symbol, new_symbol, "conflicting return types");

        conflicts.emplace_back(old_t.return_type(), new_t.return_type());
      }

      code_typet::parameterst::const_iterator
        n_it=new_t.parameters().begin(),
        o_it=old_t.parameters().begin();
      for( ;
          o_it!=old_t.parameters().end() &&
          n_it!=new_t.parameters().end();
          ++o_it, ++n_it)
      {
        if(o_it->type() != n_it->type())
          conflicts.push_back(
            std::make_pair(o_it->type(), n_it->type()));
      }
      if(o_it!=old_t.parameters().end())
      {
        if(!new_t.has_ellipsis() && old_symbol.value.is_not_nil())
        {
          diag.error(
            old_symbol,
            new_symbol,
            "conflicting parameter counts of function declarations");

          // error logged, continue typechecking other symbols
          return;
        }

        replace=new_symbol.value.is_not_nil();
      }
      else if(n_it!=new_t.parameters().end())
      {
        if(!old_t.has_ellipsis() && new_symbol.value.is_not_nil())
        {
          diag.error(
            old_symbol,
            new_symbol,
            "conflicting parameter counts of function declarations");

          // error logged, continue typechecking other symbols
          return;
        }

        replace=new_symbol.value.is_not_nil();
      }

      while(!conflicts.empty())
      {
        const typet &t1=follow_tags_symbols(ns, conflicts.front().first);
        const typet &t2=follow_tags_symbols(ns, conflicts.front().second);

        // different pointer arguments without implementation may work
        if(
          (t1.id() == ID_pointer || t2.id() == ID_pointer) &&
          pointer_offset_bits(t1, ns) == pointer_offset_bits(t2, ns) &&
          old_symbol.value.is_nil() && new_symbol.value.is_nil())
        {
          if(warn_msg.empty())
            warn_msg="different pointer types in extern function";
        }
        // different pointer arguments with implementation - the
        // implementation is always right, even though such code may
        // be severely broken
        else if((t1.id()==ID_pointer || t2.id()==ID_pointer) &&
                pointer_offset_bits(t1, ns)==pointer_offset_bits(t2, ns) &&
                old_symbol.value.is_nil()!=new_symbol.value.is_nil())
        {
          if(warn_msg.empty())
          {
            warn_msg="pointer parameter types differ between "
                     "declaration and definition";
          }

          replace=new_symbol.value.is_not_nil();
        }
        // transparent union with (or entirely without) implementation is
        // ok -- this primarily helps all those people that don't get
        // _GNU_SOURCE consistent
        else if((t1.id()==ID_union &&
                 (t1.get_bool(ID_C_transparent_union) ||
                  conflicts.front().first.get_bool(ID_C_transparent_union))) ||
                (t2.id()==ID_union &&
                 (t2.get_bool(ID_C_transparent_union) ||
                  conflicts.front().second.get_bool(ID_C_transparent_union))))
        {
          const bool use_old=
            t1.id()==ID_union &&
            (t1.get_bool(ID_C_transparent_union) ||
             conflicts.front().first.get_bool(ID_C_transparent_union)) &&
            new_symbol.value.is_nil();

          const union_typet &union_type=
            to_union_type(t1.id()==ID_union?t1:t2);
          const typet &src_type=t1.id()==ID_union?t2:t1;

          bool found=false;
          for(const auto &c : union_type.components())
            if(c.type() == src_type)
            {
              found=true;
              if(warn_msg.empty())
                warn_msg="conflict on transparent union parameter in function";
              replace=!use_old;
            }

          if(!found)
            break;
        }
        // different non-pointer arguments with implementation - the
        // implementation is always right, even though such code may
        // be severely broken
        else if(pointer_offset_bits(t1, ns)==pointer_offset_bits(t2, ns) &&
                old_symbol.value.is_nil()!=new_symbol.value.is_nil())
        {
          if(warn_msg.empty())
            warn_msg="non-pointer parameter types differ between "
                     "declaration and definition";
          replace=new_symbol.value.is_not_nil();
        }
        else
          break;

        conflicts.pop_front();
      }

      if(!conflicts.empty())
      {
        diag.detailed_conflict_report(
          old_symbol,
          new_symbol,
          conflicts.front().first,
          conflicts.front().second);

        diag.error(old_symbol, new_symbol, "conflicting function declarations");

        // error logged, continue typechecking other symbols
        return;
      }
      else
      {
        // warns about the first inconsistency
        diag.warning(old_symbol, new_symbol, warn_msg);

        if(replace)
        {
          old_symbol.type=new_symbol.type;
          old_symbol.location=new_symbol.location;
        }
      }
    }

    object_type_updates.insert(
      old_symbol.symbol_expr(), old_symbol.symbol_expr());
  }

  if(!new_symbol.value.is_nil())
  {
    if(old_symbol.value.is_nil())
    {
      // the one with body wins!
      rename_new_symbol(new_symbol.value);
      rename_new_symbol(new_symbol.type);
      old_symbol.value=new_symbol.value;
      old_symbol.type=new_symbol.type; // for parameter identifiers
      old_symbol.is_weak=new_symbol.is_weak;
      old_symbol.location=new_symbol.location;
      old_symbol.is_macro=new_symbol.is_macro;

      // replace any previous update
      object_type_updates.erase(old_symbol.name);
      object_type_updates.insert(
        old_symbol.symbol_expr(), old_symbol.symbol_expr());
    }
    else if(to_code_type(old_symbol.type).get_inlined())
    {
      // ok, silently ignore
    }
    else if(old_symbol.type == new_symbol.type)
    {
      // keep the one in old_symbol -- libraries come last!
      messaget log{message_handler};
      log.debug().source_location = new_symbol.location;
      log.debug() << "function '" << old_symbol.name << "' in module '"
                  << new_symbol.module
                  << "' is shadowed by a definition in module '"
                  << old_symbol.module << "'" << messaget::eom;
    }
    else
    {
      diag.error(old_symbol, new_symbol, "duplicate definition of function");
    }
  }
}

bool linkingt::adjust_object_type_rec(
  const typet &t1,
  const typet &t2,
  adjust_type_infot &info)
{
  if(t1 == t2)
    return false;

  if(
    t1.id() == ID_struct_tag || t1.id() == ID_union_tag ||
    t1.id() == ID_c_enum_tag)
  {
    const irep_idt &identifier = to_tag_type(t1).get_identifier();

    if(info.o_symbols.insert(identifier).second)
    {
      bool result=
        adjust_object_type_rec(follow_tags_symbols(ns, t1), t2, info);
      info.o_symbols.erase(identifier);

      return result;
    }

    return false;
  }
  else if(
    t2.id() == ID_struct_tag || t2.id() == ID_union_tag ||
    t2.id() == ID_c_enum_tag)
  {
    const irep_idt &identifier = to_tag_type(t2).get_identifier();

    if(info.n_symbols.insert(identifier).second)
    {
      bool result=
        adjust_object_type_rec(t1, follow_tags_symbols(ns, t2), info);
      info.n_symbols.erase(identifier);

      return result;
    }

    return false;
  }
  else if(t1.id()==ID_pointer && t2.id()==ID_array)
  {
    info.set_to_new=true; // store new type

    return false;
  }
  else if(t1.id()==ID_array && t2.id()==ID_pointer)
  {
    // ignore
    return false;
  }
  else if(
    t1.id() == ID_struct && to_struct_type(t1).is_incomplete() &&
    t2.id() == ID_struct && !to_struct_type(t2).is_incomplete())
  {
    info.set_to_new=true; // store new type

    return false;
  }
  else if(
    t1.id() == ID_union && to_union_type(t1).is_incomplete() &&
    t2.id() == ID_union && !to_union_type(t2).is_incomplete())
  {
    info.set_to_new = true; // store new type

    return false;
  }
  else if(
    t1.id() == ID_struct && !to_struct_type(t1).is_incomplete() &&
    t2.id() == ID_struct && to_struct_type(t2).is_incomplete())
  {
    // ignore
    return false;
  }
  else if(
    t1.id() == ID_union && !to_union_type(t1).is_incomplete() &&
    t2.id() == ID_union && to_union_type(t2).is_incomplete())
  {
    // ignore
    return false;
  }
  else if(t1.id()!=t2.id())
  {
    // type classes do not match and can't be fixed
    return true;
  }

  if(t1.id()==ID_pointer)
  {
    linking_diagnosticst diag{message_handler, ns};
#if 0
    bool s=info.set_to_new;
    if(adjust_object_type_rec(t1.subtype(), t2.subtype(), info))
    {
      diag.warning(
        info.old_symbol,
        info.new_symbol,
        "conflicting pointer types for variable");
      info.set_to_new=s;
    }
#else
    diag.warning(
      info.old_symbol,
      info.new_symbol,
      "conflicting pointer types for variable");
#endif

    if(info.old_symbol.is_extern && !info.new_symbol.is_extern)
    {
      info.set_to_new = true; // store new type
    }

    return false;
  }
  else if(
    t1.id() == ID_array &&
    !adjust_object_type_rec(
      to_array_type(t1).element_type(), to_array_type(t2).element_type(), info))
  {
    // still need to compare size
    const exprt &old_size=to_array_type(t1).size();
    const exprt &new_size=to_array_type(t2).size();

    if(
      (old_size.is_nil() && new_size.is_not_nil()) ||
      (old_size.is_constant() && to_constant_expr(old_size).is_zero() &&
       new_size.is_not_nil()) ||
      info.old_symbol.is_weak)
    {
      info.set_to_new=true; // store new type
    }
    else if(
      new_size.is_nil() ||
      (new_size.is_constant() && to_constant_expr(new_size).is_zero()) ||
      info.new_symbol.is_weak)
    {
      // ok, we will use the old type
    }
    else
    {
      if(new_size.type() != old_size.type())
      {
        linking_diagnosticst diag{message_handler, ns};
        diag.error(
          info.old_symbol,
          info.new_symbol,
          "conflicting array sizes for variable");

        // error logged, continue typechecking other symbols
        return true;
      }

      exprt maybe_eq = simplify_expr(equal_exprt{old_size, new_size}, ns);
      if(!maybe_eq.is_constant() || !to_constant_expr(maybe_eq).is_true())
      {
        linking_diagnosticst diag{message_handler, ns};
        diag.error(
          info.old_symbol,
          info.new_symbol,
          "conflicting array sizes for variable");

        // error logged, continue typechecking other symbols
        return true;
      }
    }

    return false;
  }
  else if(t1.id()==ID_struct || t1.id()==ID_union)
  {
    const struct_union_typet::componentst &components1=
      to_struct_union_type(t1).components();

    const struct_union_typet::componentst &components2=
      to_struct_union_type(t2).components();

    struct_union_typet::componentst::const_iterator
      it1=components1.begin(), it2=components2.begin();
    for( ;
        it1!=components1.end() && it2!=components2.end();
        ++it1, ++it2)
    {
      if(it1->get_name()!=it2->get_name() ||
         adjust_object_type_rec(it1->type(), it2->type(), info))
        return true;
    }
    if(it1!=components1.end() || it2!=components2.end())
      return true;

    return false;
  }

  return true;
}

bool linkingt::adjust_object_type(
  const symbolt &old_symbol,
  const symbolt &new_symbol,
  bool &set_to_new)
{
  const typet &old_type=follow_tags_symbols(ns, old_symbol.type);
  const typet &new_type=follow_tags_symbols(ns, new_symbol.type);

  adjust_type_infot info(old_symbol, new_symbol);
  bool result=adjust_object_type_rec(old_type, new_type, info);
  set_to_new=info.set_to_new;

  return result;
}

void linkingt::duplicate_object_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  // both are variables
  bool set_to_new = false;

  if(old_symbol.type != new_symbol.type)
  {
    bool failed=
      adjust_object_type(old_symbol, new_symbol, set_to_new);

    if(failed)
    {
      const typet &old_type=follow_tags_symbols(ns, old_symbol.type);

      linking_diagnosticst diag{message_handler, ns};

      // provide additional diagnostic output for
      // struct/union/array/enum
      if(old_type.id()==ID_struct ||
         old_type.id()==ID_union ||
         old_type.id()==ID_array ||
         old_type.id()==ID_c_enum)
      {
        diag.detailed_conflict_report(
          old_symbol, new_symbol, old_symbol.type, new_symbol.type);
      }

      diag.error(old_symbol, new_symbol, "conflicting types for variable");

      // error logged, continue typechecking other symbols
      return;
    }
    else if(set_to_new)
      old_symbol.type=new_symbol.type;

    object_type_updates.insert(
      old_symbol.symbol_expr(), old_symbol.symbol_expr());
  }

  // care about initializers

  if(!new_symbol.value.is_nil())
  {
    if(old_symbol.value.is_nil() ||
       old_symbol.is_weak)
    {
      // new_symbol wins
      old_symbol.value=new_symbol.value;
      old_symbol.is_macro=new_symbol.is_macro;
    }
    else if(!new_symbol.is_weak)
    {
      // try simplifier
      exprt tmp_old=old_symbol.value,
            tmp_new=new_symbol.value;

      simplify(tmp_old, ns);
      simplify(tmp_new, ns);

      if(tmp_old == tmp_new)
      {
        // ok, the same
      }
      else
      {
        messaget log{message_handler};
        log.warning().source_location = new_symbol.location;

        log.warning() << "conflicting initializers for"
                      << " variable '" << old_symbol.name << "'\n";
        log.warning() << "using old value in module " << old_symbol.module
                      << " " << old_symbol.value.find_source_location() << '\n'
                      << from_expr(ns, old_symbol.name, tmp_old) << '\n';
        log.warning() << "ignoring new value in module " << new_symbol.module
                      << " " << new_symbol.value.find_source_location() << '\n'
                      << from_expr(ns, new_symbol.name, tmp_new)
                      << messaget::eom;
      }
    }
  }
  else if(set_to_new && !old_symbol.value.is_nil())
  {
    // the type has been updated, now make sure that the initialising assignment
    // will have matching types
    old_symbol.value = typecast_exprt(old_symbol.value, old_symbol.type);
  }
}

void linkingt::duplicate_non_type_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  // we do not permit different contracts with the same name to be defined, or
  // cases where only one of the symbols is a contract
  if(
    old_symbol.is_property != new_symbol.is_property ||
    (old_symbol.is_property && new_symbol.is_property &&
     old_symbol.type != new_symbol.type))
  {
    linking_diagnosticst diag{message_handler, ns};
    diag.error(old_symbol, new_symbol, "conflict on code contract");
  }

  // see if it is a function or a variable

  bool is_code_old_symbol=old_symbol.type.id()==ID_code;
  bool is_code_new_symbol=new_symbol.type.id()==ID_code;

  if(is_code_old_symbol!=is_code_new_symbol)
  {
    linking_diagnosticst diag{message_handler, ns};
    diag.error(old_symbol, new_symbol, "conflicting definition for symbol");

    // error logged, continue typechecking other symbols
    return;
  }

  if(is_code_old_symbol)
    duplicate_code_symbol(old_symbol, new_symbol);
  else
    duplicate_object_symbol(old_symbol, new_symbol);

  // care about flags

  if(old_symbol.is_extern && !new_symbol.is_extern)
    old_symbol.location=new_symbol.location;

  // it's enough that one isn't extern for the final one not to be
  old_symbol.is_extern=old_symbol.is_extern && new_symbol.is_extern;
}

void linkingt::duplicate_type_symbol(
  symbolt &old_symbol,
  const symbolt &new_symbol)
{
  PRECONDITION(new_symbol.is_type);

  if(!old_symbol.is_type)
  {
    linking_diagnosticst diag{message_handler, ns};
    diag.error(old_symbol, new_symbol, "conflicting definition for symbol");

    // error logged, continue typechecking other symbols
    return;
  }

  if(old_symbol.type==new_symbol.type)
    return;

  if(
    old_symbol.type.id() == ID_struct &&
    to_struct_type(old_symbol.type).is_incomplete() &&
    new_symbol.type.id() == ID_struct &&
    !to_struct_type(new_symbol.type).is_incomplete())
  {
    old_symbol.type=new_symbol.type;
    old_symbol.location=new_symbol.location;
    return;
  }

  if(
    old_symbol.type.id() == ID_struct &&
    !to_struct_type(old_symbol.type).is_incomplete() &&
    new_symbol.type.id() == ID_struct &&
    to_struct_type(new_symbol.type).is_incomplete())
  {
    // ok, keep old
    return;
  }

  if(
    old_symbol.type.id() == ID_union &&
    to_union_type(old_symbol.type).is_incomplete() &&
    new_symbol.type.id() == ID_union &&
    !to_union_type(new_symbol.type).is_incomplete())
  {
    old_symbol.type=new_symbol.type;
    old_symbol.location=new_symbol.location;
    return;
  }

  if(
    old_symbol.type.id() == ID_union &&
    !to_union_type(old_symbol.type).is_incomplete() &&
    new_symbol.type.id() == ID_union &&
    to_union_type(new_symbol.type).is_incomplete())
  {
    // ok, keep old
    return;
  }

  if(
    old_symbol.type.id() == ID_array && new_symbol.type.id() == ID_array &&
    to_array_type(old_symbol.type).element_type() ==
      to_array_type(new_symbol.type).element_type())
  {
    if(to_array_type(old_symbol.type).size().is_nil() &&
       to_array_type(new_symbol.type).size().is_not_nil())
    {
      to_array_type(old_symbol.type).size()=
        to_array_type(new_symbol.type).size();
      return;
    }

    if(to_array_type(new_symbol.type).size().is_nil() &&
       to_array_type(old_symbol.type).size().is_not_nil())
    {
      // ok, keep old
      return;
    }
  }

  linking_diagnosticst diag{message_handler, ns};

  diag.detailed_conflict_report(
    old_symbol, new_symbol, old_symbol.type, new_symbol.type);

  diag.error(
    old_symbol, new_symbol, "unexpected difference between type symbols");
}

linkingt::renamingt linkingt::needs_renaming_type(
  const symbolt &old_symbol,
  const symbolt &new_symbol)
{
  PRECONDITION(new_symbol.is_type);

  if(!old_symbol.is_type)
    return renamingt::RENAME_NEW;

  if(old_symbol.type==new_symbol.type)
    return renamingt::NO_RENAMING;

  if(
    old_symbol.type.id() == ID_struct &&
    to_struct_type(old_symbol.type).is_incomplete() &&
    new_symbol.type.id() == ID_struct &&
    !to_struct_type(new_symbol.type).is_incomplete())
  {
    return renamingt::NO_RENAMING; // not different
  }

  if(
    old_symbol.type.id() == ID_struct &&
    !to_struct_type(old_symbol.type).is_incomplete() &&
    new_symbol.type.id() == ID_struct &&
    to_struct_type(new_symbol.type).is_incomplete())
  {
    return renamingt::NO_RENAMING; // not different
  }

  if(
    old_symbol.type.id() == ID_union &&
    to_union_type(old_symbol.type).is_incomplete() &&
    new_symbol.type.id() == ID_union &&
    !to_union_type(new_symbol.type).is_incomplete())
  {
    return renamingt::NO_RENAMING; // not different
  }

  if(
    old_symbol.type.id() == ID_union &&
    !to_union_type(old_symbol.type).is_incomplete() &&
    new_symbol.type.id() == ID_union &&
    to_union_type(new_symbol.type).is_incomplete())
  {
    return renamingt::NO_RENAMING; // not different
  }

  if(
    old_symbol.type.id() == ID_array && new_symbol.type.id() == ID_array &&
    to_array_type(old_symbol.type).element_type() ==
      to_array_type(new_symbol.type).element_type())
  {
    if(to_array_type(old_symbol.type).size().is_nil() &&
       to_array_type(new_symbol.type).size().is_not_nil())
    {
      return renamingt::NO_RENAMING; // not different
    }

    if(to_array_type(new_symbol.type).size().is_nil() &&
       to_array_type(old_symbol.type).size().is_not_nil())
    {
      return renamingt::NO_RENAMING; // not different
    }
  }

  return renamingt::RENAME_NEW; // different
}

static void do_type_dependencies(
  const symbol_table_baset &src_symbol_table,
  std::unordered_set<irep_idt> &needs_to_be_renamed,
  message_handlert &message_handler)
{
  // Any type that uses a symbol that will be renamed also
  // needs to be renamed, and so on, until saturation.

  // X -> Y iff Y uses X for new symbol type IDs X and Y
  std::unordered_map<irep_idt, std::unordered_set<irep_idt>> used_by;

  for(const auto &symbol_pair : src_symbol_table.symbols)
  {
    if(symbol_pair.second.is_type)
    {
      // find type and array-size symbols
      find_symbols_sett symbols_used;
      find_type_and_expr_symbols(symbol_pair.second.type, symbols_used);

      for(const auto &symbol_used : symbols_used)
      {
        used_by[symbol_used].insert(symbol_pair.first);
      }
    }
  }

  std::deque<irep_idt> queue(
    needs_to_be_renamed.begin(), needs_to_be_renamed.end());

  while(!queue.empty())
  {
    irep_idt id = queue.back();
    queue.pop_back();

    const std::unordered_set<irep_idt> &u = used_by[id];

    for(const auto &dep : u)
      if(needs_to_be_renamed.insert(dep).second)
      {
        queue.push_back(dep);
        #ifdef DEBUG
        messaget log{message_handler};
        log.debug() << "LINKING: needs to be renamed (dependency): " << dep
                    << messaget::eom;
#endif
      }
  }
}

std::unordered_map<irep_idt, irep_idt> linkingt::rename_symbols(
  const symbol_table_baset &src_symbol_table,
  const std::unordered_set<irep_idt> &needs_to_be_renamed)
{
  std::unordered_map<irep_idt, irep_idt> new_identifiers;
  namespacet src_ns(src_symbol_table);

  for(const irep_idt &id : needs_to_be_renamed)
  {
    const symbolt &new_symbol = src_ns.lookup(id);

    irep_idt new_identifier;

    if(new_symbol.is_type)
      new_identifier=type_to_name(src_ns, id, new_symbol.type);
    else
      new_identifier = rename(src_symbol_table, id);

    new_identifiers.emplace(id, new_identifier);

#ifdef DEBUG
    messaget log{message_handler};
    log.debug() << "LINKING: renaming " << id << " to " << new_identifier
                << messaget::eom;
#endif

    if(new_symbol.is_type)
      rename_new_symbol.insert_type(id, new_identifier);
    else
      rename_new_symbol.insert_expr(id, new_identifier);
  }

  return new_identifiers;
}

void linkingt::copy_symbols(
  const symbol_table_baset &src_symbol_table,
  const std::unordered_map<irep_idt, irep_idt> &new_identifiers)
{
  std::map<irep_idt, symbolt> src_symbols;
  // First apply the renaming
  for(const auto &named_symbol : src_symbol_table.symbols)
  {
    symbolt symbol=named_symbol.second;
    // apply the renaming
    rename_new_symbol(symbol.type);
    rename_new_symbol(symbol.value);
    auto it = new_identifiers.find(named_symbol.first);
    if(it != new_identifiers.end())
      symbol.name = it->second;

    src_symbols.emplace(named_symbol.first, std::move(symbol));
  }

  // Move over all the non-colliding ones
  std::unordered_set<irep_idt> collisions;

  for(const auto &named_symbol : src_symbols)
  {
    // renamed?
    if(named_symbol.first!=named_symbol.second.name)
    {
      // new
      main_symbol_table.add(named_symbol.second);
    }
    else
    {
      if(!main_symbol_table.has_symbol(named_symbol.first))
      {
        // new
        main_symbol_table.add(named_symbol.second);
      }
      else
        collisions.insert(named_symbol.first);
    }
  }

  // Now do the collisions
  for(const irep_idt &collision : collisions)
  {
    symbolt &old_symbol = main_symbol_table.get_writeable_ref(collision);
    symbolt &new_symbol=src_symbols.at(collision);

    if(new_symbol.is_type)
      duplicate_type_symbol(old_symbol, new_symbol);
    else
      duplicate_non_type_symbol(old_symbol, new_symbol);
  }

  // Apply type updates to initializers
  for(auto it = main_symbol_table.begin(); it != main_symbol_table.end(); ++it)
  {
    if(
      !it->second.is_type && !it->second.is_macro &&
      it->second.value.is_not_nil())
    {
      object_type_updates(it.get_writeable_symbol().value);
    }
  }
}

bool linkingt::link(const symbol_table_baset &src_symbol_table)
{
  const unsigned errors_before =
    message_handler.get_message_count(messaget::M_ERROR);

  // We do this in three phases. We first figure out which symbols need to
  // be renamed, and then build the renaming, and finally apply this
  // renaming in the second pass over the symbol table.

  // PHASE 1: identify symbols to be renamed

  std::unordered_set<irep_idt> needs_to_be_renamed;

  for(const auto &symbol_pair : src_symbol_table.symbols)
  {
    symbol_table_baset::symbolst::const_iterator m_it =
      main_symbol_table.symbols.find(symbol_pair.first);

    if(m_it != main_symbol_table.symbols.end())
    {
      // duplicate
      switch(needs_renaming(m_it->second, symbol_pair.second))
      {
      case renamingt::NO_RENAMING:
        break;
      case renamingt::RENAME_OLD:
      {
        symbolt renamed_symbol = m_it->second;
        renamed_symbol.name = rename(src_symbol_table, symbol_pair.first);
        if(m_it->second.is_type)
          rename_main_symbol.insert_type(m_it->first, renamed_symbol.name);
        else
          rename_main_symbol.insert_expr(m_it->first, renamed_symbol.name);
        main_symbol_table.erase(m_it);
        main_symbol_table.insert(std::move(renamed_symbol));
        break;
      }
      case renamingt::RENAME_NEW:
      {
        needs_to_be_renamed.insert(symbol_pair.first);
#ifdef DEBUG
        messaget log{message_handler};
        log.debug() << "LINKING: needs to be renamed: " << symbol_pair.first
                    << messaget::eom;
#endif
        break;
      }
      }
    }
  }

  // rename within main symbol table
  for(auto &symbol_pair : main_symbol_table)
  {
    symbolt tmp = symbol_pair.second;
    bool unmodified = rename_main_symbol(tmp.value);
    unmodified &= rename_main_symbol(tmp.type);
    if(!unmodified)
    {
      symbolt *sym_ptr = main_symbol_table.get_writeable(symbol_pair.first);
      CHECK_RETURN(sym_ptr);
      *sym_ptr = std::move(tmp);
    }
  }

  // renaming types may trigger further renaming
  do_type_dependencies(src_symbol_table, needs_to_be_renamed, message_handler);

  // PHASE 2: actually rename them
  auto new_identifiers = rename_symbols(src_symbol_table, needs_to_be_renamed);

  // PHASE 3: copy new symbols to main table
  copy_symbols(src_symbol_table, new_identifiers);

  return message_handler.get_message_count(messaget::M_ERROR) != errors_before;
}

bool linking(
  symbol_table_baset &dest_symbol_table,
  const symbol_table_baset &new_symbol_table,
  message_handlert &message_handler)
{
  linkingt linking(dest_symbol_table, message_handler);

  return linking.link(new_symbol_table);
}
