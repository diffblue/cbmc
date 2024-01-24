/*******************************************************************\

Module: ANSI-C Linking

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// ANSI-C Linking

#include "linking_diagnostics.h"

#include <util/c_types.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/namespace.h>

#include <langapi/language_util.h>

#include <unordered_set>

static const typet &follow_tags_symbols(const namespacet &ns, const typet &type)
{
  if(type.id() == ID_c_enum_tag)
    return ns.follow_tag(to_c_enum_tag_type(type));
  else if(type.id() == ID_struct_tag)
    return ns.follow_tag(to_struct_tag_type(type));
  else if(type.id() == ID_union_tag)
    return ns.follow_tag(to_union_tag_type(type));
  else
    return type;
}

std::string linking_diagnosticst::type_to_string_verbose(
  const symbolt &symbol,
  const typet &type) const
{
  const typet &followed = follow_tags_symbols(ns, type);

  if(followed.id() == ID_struct || followed.id() == ID_union)
  {
    std::string result = followed.id_string();

    const std::string &tag = followed.get_string(ID_tag);
    if(!tag.empty())
      result += " " + tag;

    if(to_struct_union_type(followed).is_incomplete())
    {
      result += "   (incomplete)";
    }
    else
    {
      result += " {\n";

      for(const auto &c : to_struct_union_type(followed).components())
      {
        const typet &subtype = c.type();
        result += "  ";
        result += from_type(ns, symbol.name, subtype);
        result += ' ';

        if(!c.get_base_name().empty())
          result += id2string(c.get_base_name());
        else
          result += id2string(c.get_name());

        result += ";\n";
      }

      result += '}';
    }

    return result;
  }
  else if(followed.id() == ID_pointer)
  {
    return type_to_string_verbose(
             symbol, to_pointer_type(followed).base_type()) +
           " *";
  }

  return from_type(ns, symbol.name, type);
}

bool linking_diagnosticst::detailed_conflict_report_rec(
  const symbolt &old_symbol,
  const symbolt &new_symbol,
  const typet &type1,
  const typet &type2,
  unsigned depth,
  exprt &conflict_path)
{
  bool conclusive = false;

#ifdef DEBUG
  messaget log{message_handler};
  log.debug() << "<BEGIN DEPTH " << depth << ">" << messaget::eom;
#endif

  std::string msg;

  const typet &t1 = follow_tags_symbols(ns, type1);
  const typet &t2 = follow_tags_symbols(ns, type2);

  if(t1.id() != t2.id())
  {
    msg = "type classes differ";
    conclusive = true;
  }
  else if(t1.id() == ID_pointer || t1.id() == ID_array)
  {
    if(
      depth > 0 &&
      to_type_with_subtype(t1).subtype() != to_type_with_subtype(t2).subtype())
    {
      if(conflict_path.type().id() == ID_pointer)
        conflict_path = dereference_exprt(conflict_path);

      conclusive = detailed_conflict_report_rec(
        old_symbol,
        new_symbol,
        to_type_with_subtype(t1).subtype(),
        to_type_with_subtype(t2).subtype(),
        depth - 1,
        conflict_path);
    }
    else if(t1.id() == ID_pointer)
      msg = "pointer types differ";
    else
      msg = "array types differ";
  }
  else if(t1.id() == ID_struct || t1.id() == ID_union)
  {
    const struct_union_typet::componentst &components1 =
      to_struct_union_type(t1).components();

    const struct_union_typet::componentst &components2 =
      to_struct_union_type(t2).components();

    exprt conflict_path_before = conflict_path;

    if(components1.size() != components2.size())
    {
      msg = "number of members is different (";
      msg += std::to_string(components1.size()) + '/';
      msg += std::to_string(components2.size()) + ')';
      conclusive = true;
    }
    else
    {
      for(std::size_t i = 0; i < components1.size(); ++i)
      {
        const typet &subtype1 = components1[i].type();
        const typet &subtype2 = components2[i].type();

        if(components1[i].get_name() != components2[i].get_name())
        {
          msg = "names of member " + std::to_string(i) + " differ (";
          msg += id2string(components1[i].get_name()) + '/';
          msg += id2string(components2[i].get_name()) + ')';
          conclusive = true;
        }
        else if(subtype1 != subtype2)
        {
          typedef std::unordered_set<typet, irep_hash> type_sett;
          type_sett parent_types;

          exprt e = conflict_path_before;
          while(e.id() == ID_dereference || e.id() == ID_member ||
                e.id() == ID_index)
          {
            parent_types.insert(e.type());
            parent_types.insert(follow_tags_symbols(ns, e.type()));
            if(e.id() == ID_dereference)
              e = to_dereference_expr(e).pointer();
            else if(e.id() == ID_member)
              e = to_member_expr(e).compound();
            else if(e.id() == ID_index)
              e = to_index_expr(e).array();
            else
              UNREACHABLE;
          }

          if(parent_types.find(subtype1) == parent_types.end())
          {
            conflict_path = conflict_path_before;
            conflict_path.type() = t1;
            conflict_path = member_exprt(conflict_path, components1[i]);

            if(depth > 0)
            {
              conclusive = detailed_conflict_report_rec(
                old_symbol,
                new_symbol,
                subtype1,
                subtype2,
                depth - 1,
                conflict_path);
            }
          }
          else
          {
            msg = "type of member " + id2string(components1[i].get_name()) +
                  " differs (recursive)";
          }
        }

        if(conclusive)
          break;
      }
    }
  }
  else if(t1.id() == ID_c_enum)
  {
    const c_enum_typet::memberst &members1 = to_c_enum_type(t1).members();

    const c_enum_typet::memberst &members2 = to_c_enum_type(t2).members();

    if(
      to_c_enum_type(t1).underlying_type() !=
      to_c_enum_type(t2).underlying_type())
    {
      msg = "enum value types are different (";
      msg +=
        from_type(ns, old_symbol.name, to_c_enum_type(t1).underlying_type()) +
        '/';
      msg +=
        from_type(ns, new_symbol.name, to_c_enum_type(t2).underlying_type()) +
        ')';
      conclusive = true;
    }
    else if(members1.size() != members2.size())
    {
      msg = "number of enum members is different (";
      msg += std::to_string(members1.size()) + '/';
      msg += std::to_string(members2.size()) + ')';
      conclusive = true;
    }
    else
    {
      for(std::size_t i = 0; i < members1.size(); ++i)
      {
        if(members1[i].get_base_name() != members2[i].get_base_name())
        {
          msg = "names of member " + std::to_string(i) + " differ (";
          msg += id2string(members1[i].get_base_name()) + '/';
          msg += id2string(members2[i].get_base_name()) + ')';
          conclusive = true;
        }
        else if(members1[i].get_value() != members2[i].get_value())
        {
          msg = "values of member " + std::to_string(i) + " differ (";
          msg += id2string(members1[i].get_value()) + '/';
          msg += id2string(members2[i].get_value()) + ')';
          conclusive = true;
        }

        if(conclusive)
          break;
      }
    }

    msg += "\nenum declarations at\n";
    msg += t1.source_location().as_string() + " and\n";
    msg += t1.source_location().as_string();
  }
  else if(t1.id() == ID_code)
  {
    const code_typet::parameterst &parameters1 = to_code_type(t1).parameters();

    const code_typet::parameterst &parameters2 = to_code_type(t2).parameters();

    const typet &return_type1 = to_code_type(t1).return_type();
    const typet &return_type2 = to_code_type(t2).return_type();

    if(parameters1.size() != parameters2.size())
    {
      msg = "parameter counts differ (";
      msg += std::to_string(parameters1.size()) + '/';
      msg += std::to_string(parameters2.size()) + ')';
      conclusive = true;
    }
    else if(return_type1 != return_type2)
    {
      conflict_path.type() = array_typet{void_type(), nil_exprt{}};
      conflict_path = index_exprt(
        conflict_path, constant_exprt(std::to_string(-1), integer_typet()));

      if(depth > 0)
      {
        conclusive = detailed_conflict_report_rec(
          old_symbol,
          new_symbol,
          return_type1,
          return_type2,
          depth - 1,
          conflict_path);
      }
      else
        msg = "return types differ";
    }
    else
    {
      for(std::size_t i = 0; i < parameters1.size(); i++)
      {
        const typet &subtype1 = parameters1[i].type();
        const typet &subtype2 = parameters2[i].type();

        if(subtype1 != subtype2)
        {
          conflict_path.type() = array_typet{void_type(), nil_exprt{}};
          conflict_path = index_exprt(
            conflict_path, constant_exprt(std::to_string(i), integer_typet()));

          if(depth > 0)
          {
            conclusive = detailed_conflict_report_rec(
              old_symbol,
              new_symbol,
              subtype1,
              subtype2,
              depth - 1,
              conflict_path);
          }
          else
            msg = "parameter types differ";
        }

        if(conclusive)
          break;
      }
    }
  }
  else
  {
    msg = "conflict on POD";
    conclusive = true;
  }

  if(conclusive && !msg.empty())
  {
#ifndef DEBUG
    messaget log{message_handler};
#endif
    log.error() << '\n';
    log.error() << "reason for conflict at "
                << from_expr(ns, irep_idt(), conflict_path) << ": " << msg
                << '\n';

    log.error() << '\n';
    log.error() << type_to_string_verbose(old_symbol, t1) << '\n';
    log.error() << type_to_string_verbose(new_symbol, t2) << '\n'
                << messaget::eom;
  }

#ifdef DEBUG
  log.debug() << "<END DEPTH " << depth << ">" << messaget::eom;
#endif

  return conclusive;
}

void linking_diagnosticst::error(
  const symbolt &old_symbol,
  const symbolt &new_symbol,
  const std::string &msg)
{
  messaget log{message_handler};
  log.error().source_location = new_symbol.location;

  log.error() << msg << " '" << old_symbol.display_name() << "'" << '\n';
  log.error() << "old definition in module '" << old_symbol.module << "' "
              << old_symbol.location << '\n'
              << type_to_string_verbose(old_symbol) << '\n';
  log.error() << "new definition in module '" << new_symbol.module << "' "
              << new_symbol.location << '\n'
              << type_to_string_verbose(new_symbol) << messaget::eom;
}

void linking_diagnosticst::warning(
  const symbolt &old_symbol,
  const symbolt &new_symbol,
  const std::string &msg)
{
  messaget log{message_handler};
  log.warning().source_location = new_symbol.location;

  log.warning() << msg << " '" << old_symbol.display_name() << "'\n";
  log.warning() << "old definition in module " << old_symbol.module << " "
                << old_symbol.location << '\n'
                << type_to_string_verbose(old_symbol) << '\n';
  log.warning() << "new definition in module " << new_symbol.module << " "
                << new_symbol.location << '\n'
                << type_to_string_verbose(new_symbol) << messaget::eom;
}
