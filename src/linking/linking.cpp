/*******************************************************************\

Module: ANSI-C Linking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Linking

#include "linking.h"

#include <cassert>
#include <deque>
#include <unordered_set>

#include <util/base_type.h>
#include <util/find_symbols.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>

#include "linking_class.h"

bool casting_replace_symbolt::replace_symbol_expr(symbol_exprt &s) const
{
  expr_mapt::const_iterator it = expr_map.find(s.get_identifier());

  if(it == expr_map.end())
    return true;

  const exprt &e = it->second;

  typet type = s.type();
  static_cast<exprt &>(s) = typecast_exprt::conditional_cast(e, type);

  return false;
}

std::string linkingt::expr_to_string(
  const irep_idt &identifier,
  const exprt &expr) const
{
  return from_expr(ns, identifier, expr);
}

std::string linkingt::type_to_string(
  const irep_idt &identifier,
  const typet &type) const
{
  return from_type(ns, identifier, type);
}

static const typet &follow_tags_symbols(
  const namespacet &ns,
  const typet &type)
{
  if(type.id() == ID_symbol_type)
    return ns.follow(type);
  else if(type.id()==ID_c_enum_tag)
    return ns.follow_tag(to_c_enum_tag_type(type));
  else if(type.id()==ID_struct_tag)
    return ns.follow_tag(to_struct_tag_type(type));
  else if(type.id()==ID_union_tag)
    return ns.follow_tag(to_union_tag_type(type));
  else
    return type;
}

std::string linkingt::type_to_string_verbose(
  const symbolt &symbol,
  const typet &type) const
{
  const typet &followed=follow_tags_symbols(ns, type);

  if(followed.id()==ID_struct || followed.id()==ID_union)
  {
    std::string result=followed.id_string();

    const std::string &tag=followed.get_string(ID_tag);
    if(tag!="")
      result+=" "+tag;
    result+=" {\n";

    for(const auto &c : to_struct_union_type(followed).components())
    {
      const typet &subtype = c.type();
      result+="  ";
      result += type_to_string(symbol.name, subtype);
      result+=' ';

      if(!c.get_base_name().empty())
        result += id2string(c.get_base_name());
      else
        result += id2string(c.get_name());

      result+=";\n";
    }

    result+='}';

    return result;
  }
  else if(followed.id()==ID_pointer)
  {
    return type_to_string_verbose(symbol, followed.subtype()) + " *";
  }
  else if(followed.id()==ID_incomplete_struct ||
          followed.id()==ID_incomplete_union)
  {
    return type_to_string(symbol.name, type) + "   (incomplete)";
  }

  return type_to_string(symbol.name, type);
}

void linkingt::detailed_conflict_report_rec(
  const symbolt &old_symbol,
  const symbolt &new_symbol,
  const typet &type1,
  const typet &type2,
  unsigned depth,
  exprt &conflict_path)
{
  #ifdef DEBUG
  debug() << "<BEGIN DEPTH " << depth << ">" << eom;
  #endif

  std::string msg;

  const typet &t1=follow_tags_symbols(ns, type1);
  const typet &t2=follow_tags_symbols(ns, type2);

  if(t1.id()!=t2.id())
    msg="type classes differ";
  else if(t1.id()==ID_pointer ||
          t1.id()==ID_array)
  {
    if(depth>0 &&
       !base_type_eq(t1.subtype(), t2.subtype(), ns))
    {
      conflict_path=dereference_exprt(conflict_path);

      detailed_conflict_report_rec(
        old_symbol,
        new_symbol,
        t1.subtype(),
        t2.subtype(),
        depth-1,
        conflict_path);
    }
    else if(t1.id()==ID_pointer)
      msg="pointer types differ";
    else
      msg="array types differ";
  }
  else if(t1.id()==ID_struct ||
          t1.id()==ID_union)
  {
    const struct_union_typet::componentst &components1=
      to_struct_union_type(t1).components();

    const struct_union_typet::componentst &components2=
      to_struct_union_type(t2).components();

    exprt conflict_path_before=conflict_path;

    if(components1.size()!=components2.size())
    {
      msg="number of members is different (";
      msg+=std::to_string(components1.size())+'/';
      msg+=std::to_string(components2.size())+')';
    }
    else
    {
      for(std::size_t i=0; i<components1.size(); ++i)
      {
        const typet &subtype1=components1[i].type();
        const typet &subtype2=components2[i].type();

        if(components1[i].get_name()!=components2[i].get_name())
        {
          msg="names of member "+std::to_string(i)+" differ (";
          msg+=id2string(components1[i].get_name())+'/';
          msg+=id2string(components2[i].get_name())+')';
          break;
        }
        else if(!base_type_eq(subtype1, subtype2, ns))
        {
          typedef std::unordered_set<typet, irep_hash> type_sett;
          type_sett parent_types;

          exprt e=conflict_path_before;
          while(e.id()==ID_dereference ||
                e.id()==ID_member ||
                e.id()==ID_index)
          {
            parent_types.insert(e.type());
            e=e.op0();
          }

          conflict_path=conflict_path_before;
          conflict_path.type()=t1;
          conflict_path=
            member_exprt(conflict_path, components1[i]);

          if(depth>0 &&
             parent_types.find(t1)==parent_types.end())
            detailed_conflict_report_rec(
              old_symbol,
              new_symbol,
              subtype1,
              subtype2,
              depth-1,
              conflict_path);
          else
          {
            msg="type of member "+
                id2string(components1[i].get_name())+
                " differs";
            if(depth>0)
            {
              std::string msg_bak;
              msg_bak.swap(msg);
              symbol_exprt c(ID_C_this);
              detailed_conflict_report_rec(
                old_symbol,
                new_symbol,
                subtype1,
                subtype2,
                depth-1,
                c);
              msg.swap(msg_bak);
            }
          }

          if(parent_types.find(t1)==parent_types.end())
            break;
        }
      }
    }
  }
  else if(t1.id()==ID_c_enum)
  {
    const c_enum_typet::memberst &members1=
      to_c_enum_type(t1).members();

    const c_enum_typet::memberst &members2=
      to_c_enum_type(t2).members();

    if(t1.subtype()!=t2.subtype())
    {
      msg="enum value types are different (";
      msg += type_to_string(old_symbol.name, t1.subtype()) + '/';
      msg += type_to_string(new_symbol.name, t2.subtype()) + ')';
    }
    else if(members1.size()!=members2.size())
    {
      msg="number of enum members is different (";
      msg+=std::to_string(members1.size())+'/';
      msg+=std::to_string(members2.size())+')';
    }
    else
    {
      for(std::size_t i=0; i<members1.size(); ++i)
      {
        if(members1[i].get_base_name()!=members2[i].get_base_name())
        {
          msg="names of member "+std::to_string(i)+" differ (";
          msg+=id2string(members1[i].get_base_name())+'/';
          msg+=id2string(members2[i].get_base_name())+')';
          break;
        }
        else if(members1[i].get_value()!=members2[i].get_value())
        {
          msg="values of member "+std::to_string(i)+" differ (";
          msg+=id2string(members1[i].get_value())+'/';
          msg+=id2string(members2[i].get_value())+')';
          break;
        }
      }
    }

    msg+="\nenum declarations at\n";
    msg+=t1.source_location().as_string()+" and\n";
    msg+=t1.source_location().as_string();
  }
  else if(t1.id()==ID_code)
  {
    const code_typet::parameterst &parameters1=
      to_code_type(t1).parameters();

    const code_typet::parameterst &parameters2=
      to_code_type(t2).parameters();

    const typet &return_type1=to_code_type(t1).return_type();
    const typet &return_type2=to_code_type(t2).return_type();

    if(parameters1.size()!=parameters2.size())
    {
      msg="parameter counts differ (";
      msg+=std::to_string(parameters1.size())+'/';
      msg+=std::to_string(parameters2.size())+')';
    }
    else if(!base_type_eq(return_type1, return_type2, ns))
    {
      conflict_path=
        index_exprt(conflict_path,
                    constant_exprt(std::to_string(-1), integer_typet()));

      if(depth>0)
        detailed_conflict_report_rec(
          old_symbol,
          new_symbol,
          return_type1,
          return_type2,
          depth-1,
          conflict_path);
      else
        msg="return types differ";
    }
    else
    {
      for(std::size_t i=0; i<parameters1.size(); i++)
      {
        const typet &subtype1=parameters1[i].type();
        const typet &subtype2=parameters2[i].type();

        if(!base_type_eq(subtype1, subtype2, ns))
        {
          conflict_path=
            index_exprt(conflict_path,
                        constant_exprt(std::to_string(i), integer_typet()));

          if(depth>0)
            detailed_conflict_report_rec(
              old_symbol,
              new_symbol,
              subtype1,
              subtype2,
              depth-1,
              conflict_path);
          else
            msg="parameter types differ";

          break;
        }
      }
    }
  }
  else
    msg="conflict on POD";

  if(!msg.empty())
  {
    error() << '\n';
    error() << "reason for conflict at " << expr_to_string("", conflict_path)
            << ": " << msg << '\n';

    error() << '\n';
    error() << type_to_string_verbose(old_symbol, t1) << '\n';
    error() << type_to_string_verbose(new_symbol, t2) << '\n';
  }

  #ifdef DEBUG
  debug() << "<END DEPTH " << depth << ">" << eom;
  #endif
}

void linkingt::link_error(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg)
{
  error().source_location=new_symbol.location;

  error() << "error: " << msg << " `"
          << old_symbol.display_name()
          << "'" << '\n';
  error() << "old definition in module `" << old_symbol.module << "' "
          << old_symbol.location << '\n'
          << type_to_string_verbose(old_symbol) << '\n';
  error() << "new definition in module `" << new_symbol.module << "' "
          << new_symbol.location << '\n'
          << type_to_string_verbose(new_symbol) << eom;
}

void linkingt::link_warning(
    const symbolt &old_symbol,
    const symbolt &new_symbol,
    const std::string &msg)
{
  warning().source_location=new_symbol.location;

  warning() << "warning: " << msg << " \""
            << old_symbol.display_name()
            << "\"" << '\n';
  warning() << "old definition in module " << old_symbol.module << " "
            << old_symbol.location << '\n'
            << type_to_string_verbose(old_symbol) << '\n';
  warning() << "new definition in module " << new_symbol.module << " "
            << new_symbol.location << '\n'
            << type_to_string_verbose(new_symbol) << eom;
}

irep_idt linkingt::rename(const irep_idt id)
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

bool linkingt::needs_renaming_non_type(
  const symbolt &old_symbol,
  const symbolt &new_symbol)
{
  // We first take care of file-local non-type symbols.
  // These are static functions, or static variables
  // inside static function bodies.
  if(new_symbol.is_file_local ||
     old_symbol.is_file_local)
    return true;

  return false;
}

void linkingt::duplicate_code_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  // Both are functions.
  if(!base_type_eq(old_symbol.type, new_symbol.type, ns))
  {
    const code_typet &old_t=to_code_type(old_symbol.type);
    const code_typet &new_t=to_code_type(new_symbol.type);

    // if one of them was an implicit declaration then only conflicts on the
    // return type are an error as we would end up with assignments with
    // mismatching types; as we currently do not patch these by inserting type
    // casts we need to fail hard
    if(!old_symbol.location.get_function().empty() &&
       old_symbol.value.is_nil())
    {
      if(base_type_eq(old_t.return_type(), new_t.return_type(), ns))
         link_warning(
           old_symbol,
           new_symbol,
           "implicit function declaration");
      else
        link_error(
          old_symbol,
          new_symbol,
          "implicit function declaration");

      old_symbol.type=new_symbol.type;
      old_symbol.location=new_symbol.location;
      old_symbol.is_weak=new_symbol.is_weak;
    }
    else if(!new_symbol.location.get_function().empty() &&
            new_symbol.value.is_nil())
    {
      if(base_type_eq(old_t.return_type(), new_t.return_type(), ns))
        link_warning(
          old_symbol,
          new_symbol,
          "ignoring conflicting implicit function declaration");
      else
        link_error(
          old_symbol,
          new_symbol,
          "implicit function declaration");
    }
    // handle (incomplete) function prototypes
    else if(base_type_eq(old_t.return_type(), new_t.return_type(), ns) &&
            ((old_t.parameters().empty() &&
              old_t.has_ellipsis() &&
              old_symbol.value.is_nil()) ||
             (new_t.parameters().empty() &&
              new_t.has_ellipsis() &&
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
        link_warning(
          old_symbol,
          new_symbol,
          "function declaration conflicts with with weak definition");
      else
        old_symbol.value.make_nil();
    }
    else if(new_symbol.is_weak)
    {
      if(new_symbol.value.is_nil() ||
         old_symbol.value.is_not_nil())
      {
        new_symbol.value.make_nil();

        link_warning(
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
      link_warning(
        old_symbol,
        new_symbol,
        "ignoring conflicting function alias declaration");
    }
    // conflicting declarations without a definition, matching return
    // types
    else if(base_type_eq(old_t.return_type(), new_t.return_type(), ns) &&
            old_symbol.value.is_nil() &&
            new_symbol.value.is_nil())
    {
      link_warning(
        old_symbol,
        new_symbol,
        "ignoring conflicting function declarations");

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
      link_error(
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

      if(!base_type_eq(old_t.return_type(), new_t.return_type(), ns))
        conflicts.push_back(
          std::make_pair(old_t.return_type(), new_t.return_type()));

      code_typet::parameterst::const_iterator
        n_it=new_t.parameters().begin(),
        o_it=old_t.parameters().begin();
      for( ;
          o_it!=old_t.parameters().end() &&
          n_it!=new_t.parameters().end();
          ++o_it, ++n_it)
      {
        if(!base_type_eq(o_it->type(), n_it->type(), ns))
          conflicts.push_back(
            std::make_pair(o_it->type(), n_it->type()));
      }
      if(o_it!=old_t.parameters().end())
      {
        if(!new_t.has_ellipsis() && old_symbol.value.is_not_nil())
        {
          link_error(
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
          link_error(
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

        // void vs. non-void return type may be acceptable if the
        // return value is never used
        if((t1.id()==ID_empty || t2.id()==ID_empty) &&
           (old_symbol.value.is_nil() || new_symbol.value.is_nil()))
        {
          if(warn_msg.empty())
            warn_msg="void/non-void return type conflict on function";
          replace=
            new_symbol.value.is_not_nil() ||
            (old_symbol.value.is_nil() && t2.id()==ID_empty);
        }
        // different pointer arguments without implementation may work
        else if((t1.id()==ID_pointer || t2.id()==ID_pointer) &&
                pointer_offset_bits(t1, ns)==pointer_offset_bits(t2, ns) &&
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
            warn_msg="pointer parameter types differ between "
                     "declaration and definition";
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
            if(base_type_eq(c.type(), src_type, ns))
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
        detailed_conflict_report(
          old_symbol,
          new_symbol,
          conflicts.front().first,
          conflicts.front().second);

        link_error(
          old_symbol,
          new_symbol,
          "conflicting function declarations");

        // error logged, continue typechecking other symbols
        return;
      }
      else
      {
        // warns about the first inconsistency
        link_warning(old_symbol, new_symbol, warn_msg);

        if(replace)
        {
          old_symbol.type=new_symbol.type;
          old_symbol.location=new_symbol.location;
        }
      }
    }
  }

  if(!new_symbol.value.is_nil())
  {
    if(old_symbol.value.is_nil())
    {
      // the one with body wins!
      rename_symbol(new_symbol.value);
      rename_symbol(new_symbol.type);
      old_symbol.value=new_symbol.value;
      old_symbol.type=new_symbol.type; // for parameter identifiers
      old_symbol.is_weak=new_symbol.is_weak;
      old_symbol.location=new_symbol.location;
      old_symbol.is_macro=new_symbol.is_macro;
    }
    else if(to_code_type(old_symbol.type).get_inlined())
    {
      // ok, silently ignore
    }
    else if(base_type_eq(old_symbol.type, new_symbol.type, ns))
    {
      // keep the one in old_symbol -- libraries come last!
      warning().source_location=new_symbol.location;

      warning() << "function `" << old_symbol.name << "' in module `"
        << new_symbol.module << "' is shadowed by a definition in module `"
        << old_symbol.module << "'" << eom;
    }
    else
      link_error(
        old_symbol,
        new_symbol,
        "duplicate definition of function");
  }
}

bool linkingt::adjust_object_type_rec(
  const typet &t1,
  const typet &t2,
  adjust_type_infot &info)
{
  if(base_type_eq(t1, t2, ns))
    return false;

  if(
    t1.id() == ID_symbol_type || t1.id() == ID_struct_tag ||
    t1.id() == ID_union_tag || t1.id() == ID_c_enum_tag)
  {
    const irep_idt &identifier=t1.get(ID_identifier);

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
    t2.id() == ID_symbol_type || t2.id() == ID_struct_tag ||
    t2.id() == ID_union_tag || t2.id() == ID_c_enum_tag)
  {
    const irep_idt &identifier=t2.get(ID_identifier);

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
  else if((t1.id()==ID_incomplete_struct && t2.id()==ID_struct) ||
          (t1.id()==ID_incomplete_union && t2.id()==ID_union))
  {
    info.set_to_new=true; // store new type

    return false;
  }
  else if((t1.id()==ID_struct && t2.id()==ID_incomplete_struct) ||
          (t1.id()==ID_union && t2.id()==ID_incomplete_union))
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
    #if 0
    bool s=info.set_to_new;
    if(adjust_object_type_rec(t1.subtype(), t2.subtype(), info))
    {
      link_warning(
        info.old_symbol,
        info.new_symbol,
        "conflicting pointer types for variable");
      info.set_to_new=s;
    }
    #else
    link_warning(
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
  else if(t1.id()==ID_array &&
          !adjust_object_type_rec(t1.subtype(), t2.subtype(), info))
  {
    // still need to compare size
    const exprt &old_size=to_array_type(t1).size();
    const exprt &new_size=to_array_type(t2).size();

    if((old_size.is_nil() && new_size.is_not_nil()) ||
       (old_size.is_zero() && new_size.is_not_nil()) ||
       info.old_symbol.is_weak)
    {
      info.set_to_new=true; // store new type
    }
    else if(new_size.is_nil() ||
            new_size.is_zero() ||
            info.new_symbol.is_weak)
    {
      // ok, we will use the old type
    }
    else
    {
      equal_exprt eq(old_size, new_size);

      if(!simplify_expr(eq, ns).is_true())
      {
        link_error(
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

  if(!base_type_eq(old_symbol.type, new_symbol.type, ns))
  {
    bool failed=
      adjust_object_type(old_symbol, new_symbol, set_to_new);

    if(failed)
    {
      const typet &old_type=follow_tags_symbols(ns, old_symbol.type);

      // provide additional diagnostic output for
      // struct/union/array/enum
      if(old_type.id()==ID_struct ||
         old_type.id()==ID_union ||
         old_type.id()==ID_array ||
         old_type.id()==ID_c_enum)
        detailed_conflict_report(
          old_symbol,
          new_symbol,
          old_symbol.type,
          new_symbol.type);

      link_error(
        old_symbol,
        new_symbol,
        "conflicting types for variable");

      // error logged, continue typechecking other symbols
      return;
    }
    else if(set_to_new)
      old_symbol.type=new_symbol.type;

    object_type_updates.insert(
      old_symbol.symbol_expr(), old_symbol.symbol_expr());
  }

  // care about initializers

  if(!new_symbol.value.is_nil() &&
     !new_symbol.value.get_bool(ID_C_zero_initializer))
  {
    if(old_symbol.value.is_nil() ||
       old_symbol.value.get_bool(ID_C_zero_initializer) ||
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

      if(base_type_eq(tmp_old, tmp_new, ns))
      {
        // ok, the same
      }
      else
      {
        warning().source_location=new_symbol.location;

        warning() << "warning: conflicting initializers for"
                  << " variable \"" << old_symbol.name << "\"\n";
        warning() << "using old value in module " << old_symbol.module << " "
                  << old_symbol.value.find_source_location() << '\n'
                  << expr_to_string(old_symbol.name, tmp_old) << '\n';
        warning() << "ignoring new value in module " << new_symbol.module << " "
                  << new_symbol.value.find_source_location() << '\n'
                  << expr_to_string(new_symbol.name, tmp_new) << eom;
      }
    }
  }
  else if(
    set_to_new && !old_symbol.value.is_nil() &&
    !old_symbol.value.get_bool(ID_C_zero_initializer))
  {
    // the type has been updated, now make sure that the initialising assignment
    // will have matching types
    old_symbol.value.make_typecast(old_symbol.type);
  }
}

void linkingt::duplicate_non_type_symbol(
  symbolt &old_symbol,
  symbolt &new_symbol)
{
  // see if it is a function or a variable

  bool is_code_old_symbol=old_symbol.type.id()==ID_code;
  bool is_code_new_symbol=new_symbol.type.id()==ID_code;

  if(is_code_old_symbol!=is_code_new_symbol)
  {
    link_error(
      old_symbol,
      new_symbol,
      "conflicting definition for symbol");

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
  assert(new_symbol.is_type);

  if(!old_symbol.is_type)
  {
    link_error(
      old_symbol,
      new_symbol,
      "conflicting definition for symbol");

    // error logged, continue typechecking other symbols
    return;
  }

  if(old_symbol.type==new_symbol.type)
    return;

  if(old_symbol.type.id()==ID_incomplete_struct &&
     new_symbol.type.id()==ID_struct)
  {
    old_symbol.type=new_symbol.type;
    old_symbol.location=new_symbol.location;
    return;
  }

  if(old_symbol.type.id()==ID_struct &&
     new_symbol.type.id()==ID_incomplete_struct)
  {
    // ok, keep old
    return;
  }

  if(old_symbol.type.id()==ID_incomplete_union &&
     new_symbol.type.id()==ID_union)
  {
    old_symbol.type=new_symbol.type;
    old_symbol.location=new_symbol.location;
    return;
  }

  if(old_symbol.type.id()==ID_union &&
     new_symbol.type.id()==ID_incomplete_union)
  {
    // ok, keep old
    return;
  }

  if(old_symbol.type.id()==ID_array &&
     new_symbol.type.id()==ID_array &&
     base_type_eq(old_symbol.type.subtype(), new_symbol.type.subtype(), ns))
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

  detailed_conflict_report(
    old_symbol,
    new_symbol,
    old_symbol.type,
    new_symbol.type);

  link_error(
    old_symbol,
    new_symbol,
    "unexpected difference between type symbols");
}

bool linkingt::needs_renaming_type(
  const symbolt &old_symbol,
  const symbolt &new_symbol)
{
  assert(new_symbol.is_type);

  if(!old_symbol.is_type)
    return true;

  if(old_symbol.type==new_symbol.type)
    return false;

  if(old_symbol.type.id()==ID_incomplete_struct &&
     new_symbol.type.id()==ID_struct)
    return false; // not different

  if(old_symbol.type.id()==ID_struct &&
     new_symbol.type.id()==ID_incomplete_struct)
    return false; // not different

  if(old_symbol.type.id()==ID_incomplete_union &&
     new_symbol.type.id()==ID_union)
    return false; // not different

  if(old_symbol.type.id()==ID_union &&
     new_symbol.type.id()==ID_incomplete_union)
    return false; // not different

  if(old_symbol.type.id()==ID_array &&
     new_symbol.type.id()==ID_array &&
     base_type_eq(old_symbol.type.subtype(), new_symbol.type.subtype(), ns))
  {
    if(to_array_type(old_symbol.type).size().is_nil() &&
       to_array_type(new_symbol.type).size().is_not_nil())
      return false; // not different

    if(to_array_type(new_symbol.type).size().is_nil() &&
       to_array_type(old_symbol.type).size().is_not_nil())
      return false; // not different
  }

  return true; // different
}

void linkingt::do_type_dependencies(
  std::unordered_set<irep_idt> &needs_to_be_renamed)
{
  // Any type that uses a symbol that will be renamed also
  // needs to be renamed, and so on, until saturation.

  used_byt used_by;

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
        debug() << "LINKING: needs to be renamed (dependency): "
                << dep << eom;
        #endif
      }
  }
}

void linkingt::rename_symbols(
  const std::unordered_set<irep_idt> &needs_to_be_renamed)
{
  namespacet src_ns(src_symbol_table);

  for(const irep_idt &id : needs_to_be_renamed)
  {
    symbolt &new_symbol=*src_symbol_table.get_writeable(id);

    irep_idt new_identifier;

    if(new_symbol.is_type)
      new_identifier=type_to_name(src_ns, id, new_symbol.type);
    else
      new_identifier=rename(id);

    new_symbol.name=new_identifier;

    #ifdef DEBUG
    debug() << "LINKING: renaming " << id << " to "
            << new_identifier << eom;
    #endif

    if(new_symbol.is_type)
      rename_symbol.insert_type(id, new_identifier);
    else
      rename_symbol.insert_expr(id, new_identifier);
  }
}

void linkingt::copy_symbols()
{
  std::map<irep_idt, symbolt> src_symbols;
  // First apply the renaming
  for(const auto &named_symbol : src_symbol_table.symbols)
  {
    symbolt symbol=named_symbol.second;
    // apply the renaming
    rename_symbol(symbol.type);
    rename_symbol(symbol.value);
    // Add to vector
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
    symbolt &old_symbol=*main_symbol_table.get_writeable(collision);
    symbolt &new_symbol=src_symbols.at(collision);

    if(new_symbol.is_type)
      duplicate_type_symbol(old_symbol, new_symbol);
    else
      duplicate_non_type_symbol(old_symbol, new_symbol);
  }

  // Apply type updates to initializers
  for(const auto &named_symbol : main_symbol_table.symbols)
  {
    if(!named_symbol.second.is_type &&
       !named_symbol.second.is_macro &&
       named_symbol.second.value.is_not_nil())
    {
      object_type_updates(
        main_symbol_table.get_writeable_ref(named_symbol.first).value);
    }
  }
}

void linkingt::typecheck()
{
  // We do this in three phases. We first figure out which symbols need to
  // be renamed, and then build the renaming, and finally apply this
  // renaming in the second pass over the symbol table.

  // PHASE 1: identify symbols to be renamed

  std::unordered_set<irep_idt> needs_to_be_renamed;

  for(const auto &symbol_pair : src_symbol_table.symbols)
  {
    symbol_tablet::symbolst::const_iterator m_it =
      main_symbol_table.symbols.find(symbol_pair.first);

    if(
      m_it != main_symbol_table.symbols.end() && // duplicate
      needs_renaming(m_it->second, symbol_pair.second))
    {
      needs_to_be_renamed.insert(symbol_pair.first);
      #ifdef DEBUG
      debug() << "LINKING: needs to be renamed: " << symbol_pair.first << eom;
      #endif
    }
  }

  // renaming types may trigger further renaming
  do_type_dependencies(needs_to_be_renamed);

  // PHASE 2: actually rename them
  rename_symbols(needs_to_be_renamed);

  // PHASE 3: copy new symbols to main table
  copy_symbols();
}

bool linking(
  symbol_tablet &dest_symbol_table,
  symbol_tablet &new_symbol_table,
  message_handlert &message_handler)
{
  linkingt linking(
    dest_symbol_table, new_symbol_table, message_handler);

  return linking.typecheck_main();
}
