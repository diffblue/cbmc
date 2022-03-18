/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#include "value_set.h"

#include <util/arith_tools.h>
#include <util/byte_operators.h>
#include <util/c_types.h>
#include <util/expr_util.h>
#include <util/format_expr.h>
#include <util/format_type.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>
#include <util/range.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <ostream>

#ifdef DEBUG
#include <iostream>
#include <util/format_expr.h>
#include <util/format_type.h>
#endif

#include "add_failed_symbols.h"

// Due to a large number of functions defined inline, `value_sett` and
// associated types are documented in its header file, `value_set.h`.

const value_sett::object_map_dt value_sett::empty_object_map{};
object_numberingt value_sett::object_numbering;

bool value_sett::field_sensitive(const irep_idt &id, const typet &type)
{
  // we always track fields on these
  if(has_prefix(id2string(id), "value_set::dynamic_object") ||
     id=="value_set::return_value" ||
     id=="value_set::memory")
    return true;

  // otherwise it has to be a struct
  return type.id() == ID_struct || type.id() == ID_struct_tag;
}

const value_sett::entryt *value_sett::find_entry(const irep_idt &id) const
{
  auto found = values.find(id);
  return !found.has_value() ? nullptr : &(found->get());
}

void value_sett::update_entry(
  const entryt &e,
  const typet &type,
  const object_mapt &new_values,
  bool add_to_sets)
{
  irep_idt index;

  if(field_sensitive(e.identifier, type))
    index=id2string(e.identifier)+e.suffix;
  else
    index=e.identifier;

  auto existing_entry = values.find(index);
  if(existing_entry.has_value())
  {
    if(add_to_sets)
    {
      if(make_union_would_change(existing_entry->get().object_map, new_values))
      {
        values.update(index, [&new_values, this](entryt &entry) {
          make_union(entry.object_map, new_values);
        });
      }
    }
    else
    {
      values.update(
        index, [&new_values](entryt &entry) { entry.object_map = new_values; });
    }
  }
  else
  {
    entryt new_entry = e;
    new_entry.object_map = new_values;
    values.insert(index, std::move(new_entry));
  }
}

value_sett::insert_actiont value_sett::get_insert_action(
  const object_mapt &dest,
  object_numberingt::number_type n,
  const offsett &offset) const
{
  auto entry=dest.read().find(n);

  if(entry==dest.read().end())
  {
    // new
    return insert_actiont::INSERT;
  }
  else if(!entry->second)
    return insert_actiont::NONE;
  else if(offset && *entry->second == *offset)
    return insert_actiont::NONE;
  else
    return insert_actiont::RESET_OFFSET;
}

bool value_sett::insert(
  object_mapt &dest,
  object_numberingt::number_type n,
  const offsett &offset) const
{
  auto insert_action = get_insert_action(dest, n, offset);
  if(insert_action == insert_actiont::NONE)
    return false;

  auto &new_offset = dest.write()[n];
  if(insert_action == insert_actiont::INSERT)
    new_offset = offset;
  else
    new_offset.reset();

  return true;
}

void value_sett::output(std::ostream &out, const std::string &indent) const
{
  values.iterate([&](const irep_idt &, const entryt &e) {
    irep_idt identifier, display_name;

    if(has_prefix(id2string(e.identifier), "value_set::dynamic_object"))
    {
      display_name = id2string(e.identifier) + e.suffix;
      identifier.clear();
    }
    else if(e.identifier == "value_set::return_value")
    {
      display_name = "RETURN_VALUE" + e.suffix;
      identifier.clear();
    }
    else
    {
#if 0
        const symbolt &symbol=ns.lookup(e.identifier);
        display_name=id2string(symbol.display_name())+e.suffix;
        identifier=symbol.name;
#else
      identifier = id2string(e.identifier);
      display_name = id2string(identifier) + e.suffix;
#endif
    }

    out << indent << display_name << " = { ";

    const object_map_dt &object_map = e.object_map.read();

    std::size_t width = 0;

    for(object_map_dt::const_iterator o_it = object_map.begin();
        o_it != object_map.end();
        o_it++)
    {
      const exprt &o = object_numbering[o_it->first];

      std::ostringstream stream;

      if(o.id() == ID_invalid || o.id() == ID_unknown)
        stream << format(o);
      else
      {
        stream << "<" << format(o) << ", ";

        if(o_it->second)
          stream << *o_it->second;
        else
          stream << '*';

        if(o.type().is_nil())
          stream << ", ?";
        else
          stream << ", " << format(o.type());

        stream << '>';
      }

      const std::string result = stream.str();
      out << result;
      width += result.size();

      object_map_dt::const_iterator next(o_it);
      next++;

      if(next != object_map.end())
      {
        out << ", ";
        if(width >= 40)
          out << "\n" << std::string(indent.size(), ' ') << "      ";
      }
    }

    out << " } \n";
  });
}

exprt value_sett::to_expr(const object_map_dt::value_type &it) const
{
  const exprt &object=object_numbering[it.first];

  if(object.id()==ID_invalid ||
     object.id()==ID_unknown)
    return object;

  object_descriptor_exprt od;

  od.object()=object;

  if(it.second)
    od.offset() = from_integer(*it.second, c_index_type());

  od.type()=od.object().type();

  return std::move(od);
}

bool value_sett::make_union(const value_sett::valuest &new_values)
{
  bool result=false;

  value_sett::valuest::delta_viewt delta_view;

  new_values.get_delta_view(values, delta_view, false);

  for(const auto &delta_entry : delta_view)
  {
    if(delta_entry.is_in_both_maps())
    {
      if(make_union_would_change(
           delta_entry.get_other_map_value().object_map,
           delta_entry.m.object_map))
      {
        values.update(delta_entry.k, [&](entryt &existing_entry) {
          make_union(existing_entry.object_map, delta_entry.m.object_map);
        });
        result = true;
      }
    }
    else
    {
      values.insert(delta_entry.k, delta_entry.m);
      result = true;
    }
  }

  return result;
}

bool value_sett::make_union_would_change(
  const object_mapt &dest,
  const object_mapt &src) const
{
  for(const auto &number_and_offset : src.read())
  {
    if(
      get_insert_action(
        dest, number_and_offset.first, number_and_offset.second) !=
      insert_actiont::NONE)
    {
      return true;
    }
  }

  return false;
}

bool value_sett::make_union(object_mapt &dest, const object_mapt &src) const
{
  bool result=false;

  for(object_map_dt::const_iterator it=src.read().begin();
      it!=src.read().end();
      it++)
  {
    if(insert(dest, *it))
      result=true;
  }

  return result;
}

bool value_sett::eval_pointer_offset(
  exprt &expr,
  const namespacet &ns) const
{
  bool mod=false;

  if(expr.id()==ID_pointer_offset)
  {
    const object_mapt reference_set =
      get_value_set(to_unary_expr(expr).op(), ns, true);

    exprt new_expr;
    mp_integer previous_offset=0;

    const object_map_dt &object_map=reference_set.read();
    for(object_map_dt::const_iterator
        it=object_map.begin();
        it!=object_map.end();
        it++)
      if(!it->second)
        return false;
      else
      {
        const exprt &object=object_numbering[it->first];
        auto ptr_offset = compute_pointer_offset(object, ns);

        if(!ptr_offset.has_value())
          return false;

        *ptr_offset += *it->second;

        if(mod && *ptr_offset != previous_offset)
          return false;

        new_expr = from_integer(*ptr_offset, expr.type());
        previous_offset = *ptr_offset;
        mod=true;
      }

    if(mod)
      expr.swap(new_expr);
  }
  else
  {
    Forall_operands(it, expr)
      mod=eval_pointer_offset(*it, ns) || mod;
  }

  return mod;
}

std::vector<exprt>
value_sett::get_value_set(exprt expr, const namespacet &ns) const
{
  const object_mapt object_map = get_value_set(std::move(expr), ns, false);
  return make_range(object_map.read())
    .map([&](const object_map_dt::value_type &pair) { return to_expr(pair); });
}

value_sett::object_mapt value_sett::get_value_set(
  exprt expr,
  const namespacet &ns,
  bool is_simplified) const
{
  if(!is_simplified)
    simplify(expr, ns);

  object_mapt dest;
  get_value_set_rec(expr, dest, "", expr.type(), ns);
  return dest;
}

/// Check if 'suffix' starts with 'field'.
/// Suffix is delimited by periods and '[]' (array access) tokens, so we're
/// looking for ".field($|[]|.)"
static bool suffix_starts_with_field(
  const std::string &suffix, const std::string &field)
{
  return
    !suffix.empty() &&
    suffix[0] == '.' &&
    suffix.compare(1, field.length(), field) == 0 &&
    (suffix.length() == field.length() + 1 ||
     suffix[field.length() + 1] == '.' ||
     suffix[field.length() + 1] == '[');
}

static std::string strip_first_field_from_suffix(
  const std::string &suffix, const std::string &field)
{
  INVARIANT(
    suffix_starts_with_field(suffix, field),
    "suffix should start with " + field);
  return suffix.substr(field.length() + 1);
}

optionalt<irep_idt> value_sett::get_index_of_symbol(
  irep_idt identifier,
  const typet &type,
  const std::string &suffix,
  const namespacet &ns) const
{
  if(
    type.id() != ID_pointer && type.id() != ID_signedbv &&
    type.id() != ID_unsignedbv && type.id() != ID_array &&
    type.id() != ID_struct && type.id() != ID_struct_tag &&
    type.id() != ID_union && type.id() != ID_union_tag)
  {
    return {};
  }

  // look it up
  irep_idt index = id2string(identifier) + suffix;
  auto *entry = find_entry(index);
  if(entry)
    return std::move(index);

  const typet &followed_type = type.id() == ID_struct_tag
                                 ? ns.follow_tag(to_struct_tag_type(type))
                                 : type.id() == ID_union_tag
                                     ? ns.follow_tag(to_union_tag_type(type))
                                     : type;

  // try first component name as suffix if not yet found
  if(followed_type.id() == ID_struct || followed_type.id() == ID_union)
  {
    const struct_union_typet &struct_union_type =
      to_struct_union_type(followed_type);

    if(!struct_union_type.components().empty())
    {
      const irep_idt &first_component_name =
        struct_union_type.components().front().get_name();

      index =
        id2string(identifier) + "." + id2string(first_component_name) + suffix;
      entry = find_entry(index);
      if(entry)
        return std::move(index);
    }
  }

  // not found? try without suffix
  entry = find_entry(identifier);
  if(entry)
    return std::move(identifier);

  return {};
}

void value_sett::get_value_set_rec(
  const exprt &expr,
  object_mapt &dest,
  const std::string &suffix,
  const typet &original_type,
  const namespacet &ns) const
{
#ifdef DEBUG
  std::cout << "GET_VALUE_SET_REC EXPR: " << format(expr) << "\n";
  std::cout << "GET_VALUE_SET_REC SUFFIX: " << suffix << '\n';
#endif

  const typet &expr_type=ns.follow(expr.type());

  if(expr.id()==ID_unknown || expr.id()==ID_invalid)
  {
    insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_index)
  {
    const typet &type = to_index_expr(expr).array().type();

    DATA_INVARIANT(
      type.id() == ID_array, "operand 0 of index expression must be an array");

    get_value_set_rec(
      to_index_expr(expr).array(), dest, "[]" + suffix, original_type, ns);
  }
  else if(expr.id()==ID_member)
  {
    const typet &type = ns.follow(to_member_expr(expr).compound().type());

    DATA_INVARIANT(
      type.id() == ID_struct || type.id() == ID_union,
      "compound of member expression must be struct or union");

    const std::string &component_name=
      expr.get_string(ID_component_name);

    get_value_set_rec(
      to_member_expr(expr).compound(),
      dest,
      "." + component_name + suffix,
      original_type,
      ns);
  }
  else if(expr.id()==ID_symbol)
  {
    auto entry_index = get_index_of_symbol(
      to_symbol_expr(expr).get_identifier(), expr_type, suffix, ns);

    if(entry_index.has_value())
      make_union(dest, find_entry(*entry_index)->object_map);
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id() == ID_nondet_symbol)
  {
    if(expr.type().id() == ID_pointer)
    {
      // we'll take the union of all objects we see, with unspecified offsets
      values.iterate([this, &dest](const irep_idt &key, const entryt &value) {
        for(const auto &object : value.object_map.read())
          insert(dest, object.first, offsett());
      });

      // we'll add null, in case it's not there yet
      insert(
        dest,
        exprt(ID_null_object, to_pointer_type(expr_type).base_type()),
        offsett());
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_if)
  {
    get_value_set_rec(
      to_if_expr(expr).true_case(), dest, suffix, original_type, ns);
    get_value_set_rec(
      to_if_expr(expr).false_case(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_address_of)
  {
    get_reference_set(to_address_of_expr(expr).object(), dest, ns);
  }
  else if(expr.id()==ID_dereference)
  {
    object_mapt reference_set;
    get_reference_set(expr, reference_set, ns);
    const object_map_dt &object_map=reference_set.read();

    if(object_map.begin()==object_map.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
    {
      for(object_map_dt::const_iterator
          it1=object_map.begin();
          it1!=object_map.end();
          it1++)
      {
        /// Do not take a reference to object_numbering's storage as we may call
        /// object_numbering.number(), which may reallocate it.
        const exprt object=object_numbering[it1->first];
        get_value_set_rec(object, dest, suffix, original_type, ns);
      }
    }
  }
  else if(expr.is_constant())
  {
    // check if NULL
    if(is_null_pointer(to_constant_expr(expr)))
    {
      insert(
        dest, exprt(ID_null_object, to_pointer_type(expr_type).base_type()), 0);
    }
    else if(expr_type.id()==ID_unsignedbv ||
            expr_type.id()==ID_signedbv)
    {
      // an integer constant got turned into a pointer
      insert(dest, exprt(ID_integer_address, unsigned_char_type()));
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_typecast)
  {
    // let's see what gets converted to what

    const auto &op = to_typecast_expr(expr).op();
    const typet &op_type = op.type();

    if(op_type.id()==ID_pointer)
    {
      // pointer-to-pointer -- we just ignore these
      get_value_set_rec(op, dest, suffix, original_type, ns);
    }
    else if(op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_signedbv)
    {
      // integer-to-pointer

      if(op.is_zero())
        insert(dest, exprt(ID_null_object, expr_type.subtype()), 0);
      else
      {
        // see if we have something for the integer
        object_mapt tmp;

        get_value_set_rec(op, tmp, suffix, original_type, ns);

        if(tmp.read().empty())
        {
          // if not, throw in integer
          insert(dest, exprt(ID_integer_address, unsigned_char_type()));
        }
        else if(tmp.read().size()==1 &&
                object_numbering[tmp.read().begin()->first].id()==ID_unknown)
        {
          // if not, throw in integer
          insert(dest, exprt(ID_integer_address, unsigned_char_type()));
        }
        else
        {
          // use as is
          dest.write().insert(tmp.read().begin(), tmp.read().end());
        }
      }
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(
    expr.id() == ID_plus || expr.id() == ID_minus || expr.id() == ID_bitor ||
    expr.id() == ID_bitand || expr.id() == ID_bitxor ||
    expr.id() == ID_bitnand || expr.id() == ID_bitnor ||
    expr.id() == ID_bitxnor)
  {
    if(expr.operands().size()<2)
      throw expr.id_string()+" expected to have at least two operands";

    object_mapt pointer_expr_set;
    optionalt<mp_integer> i;

    // special case for plus/minus and exactly one pointer
    optionalt<exprt> ptr_operand;
    if(
      expr_type.id() == ID_pointer &&
      (expr.id() == ID_plus || expr.id() == ID_minus))
    {
      bool non_const_offset = false;
      for(const auto &op : expr.operands())
      {
        if(op.type().id() == ID_pointer)
        {
          if(ptr_operand.has_value())
          {
            ptr_operand.reset();
            break;
          }

          ptr_operand = op;
        }
        else if(!non_const_offset)
        {
          auto offset = numeric_cast<mp_integer>(op);
          if(!offset.has_value())
          {
            i.reset();
            non_const_offset = true;
          }
          else
          {
            if(!i.has_value())
              i = mp_integer{0};
            i = *i + *offset;
          }
        }
      }

      if(ptr_operand.has_value() && i.has_value())
      {
        typet pointer_sub_type = ptr_operand->type().subtype();
        if(pointer_sub_type.id()==ID_empty)
          pointer_sub_type=char_type();

        auto size = pointer_offset_size(pointer_sub_type, ns);

        if(!size.has_value() || (*size) == 0)
        {
          i.reset();
        }
        else
        {
          *i *= *size;

          if(expr.id()==ID_minus)
          {
            DATA_INVARIANT(
              to_minus_expr(expr).lhs() == *ptr_operand,
              "unexpected subtraction of pointer from integer");
            i->negate();
          }
        }
      }
    }

    if(ptr_operand.has_value())
    {
      get_value_set_rec(
        *ptr_operand, pointer_expr_set, "", ptr_operand->type(), ns);
    }
    else
    {
      // we get the points-to for all operands, even integers
      forall_operands(it, expr)
      {
        get_value_set_rec(
          *it, pointer_expr_set, "", it->type(), ns);
      }
    }

    for(object_map_dt::const_iterator
        it=pointer_expr_set.read().begin();
        it!=pointer_expr_set.read().end();
        it++)
    {
      offsett offset = it->second;

      // adjust by offset
      if(offset && i.has_value())
        *offset += *i;
      else
        offset.reset();

      insert(dest, it->first, offset);
    }
  }
  else if(expr.id()==ID_mult)
  {
    // this is to do stuff like
    // (int*)((sel*(ulong)&a)+((sel^0x1)*(ulong)&b))

    if(expr.operands().size()<2)
      throw expr.id_string()+" expected to have at least two operands";

    object_mapt pointer_expr_set;

    // we get the points-to for all operands, even integers
    forall_operands(it, expr)
    {
      get_value_set_rec(
        *it, pointer_expr_set, "", it->type(), ns);
    }

    for(object_map_dt::const_iterator
        it=pointer_expr_set.read().begin();
        it!=pointer_expr_set.read().end();
        it++)
    {
      offsett offset = it->second;

      // kill any offset
      offset.reset();

      insert(dest, it->first, offset);
    }
  }
  else if(expr.id()==ID_side_effect)
  {
    const irep_idt &statement = to_side_effect_expr(expr).get_statement();

    if(statement==ID_function_call)
    {
      // these should be gone
      throw "unexpected function_call sideeffect";
    }
    else if(statement==ID_allocate)
    {
      PRECONDITION(suffix.empty());

      const typet &dynamic_type=
        static_cast<const typet &>(expr.find(ID_C_cxx_alloc_type));

      dynamic_object_exprt dynamic_object(dynamic_type);
      dynamic_object.set_instance(location_number);
      dynamic_object.valid()=true_exprt();

      insert(dest, dynamic_object, 0);
    }
    else if(statement==ID_cpp_new ||
            statement==ID_cpp_new_array)
    {
      PRECONDITION(suffix.empty());
      assert(expr_type.id()==ID_pointer);

      dynamic_object_exprt dynamic_object(
        to_pointer_type(expr_type).base_type());
      dynamic_object.set_instance(location_number);
      dynamic_object.valid()=true_exprt();

      insert(dest, dynamic_object, 0);
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_struct)
  {
    const auto &struct_components = to_struct_type(expr_type).components();
    INVARIANT(
      struct_components.size() == expr.operands().size(),
      "struct expression should have an operand per component");
    auto component_iter = struct_components.begin();
    bool found_component = false;

    // a struct constructor, which may contain addresses

    forall_operands(it, expr)
    {
      const std::string &component_name =
        id2string(component_iter->get_name());
      if(suffix_starts_with_field(suffix, component_name))
      {
        std::string remaining_suffix =
          strip_first_field_from_suffix(suffix, component_name);
        get_value_set_rec(*it, dest, remaining_suffix, original_type, ns);
        found_component = true;
      }
      ++component_iter;
    }

    if(!found_component)
    {
      // Struct field doesn't appear as expected -- this has probably been
      // cast from an incompatible type. Conservatively assume all fields may
      // be of interest.
      forall_operands(it, expr)
        get_value_set_rec(*it, dest, suffix, original_type, ns);
    }
  }
  else if(expr.id() == ID_union)
  {
    get_value_set_rec(
      to_union_expr(expr).op(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_with)
  {
    const with_exprt &with_expr = to_with_expr(expr);

    // If the suffix is empty we're looking for the whole struct:
    // default to combining both options as below.
    if(expr_type.id() == ID_struct && !suffix.empty())
    {
      irep_idt component_name = with_expr.where().get(ID_component_name);
      if(suffix_starts_with_field(suffix, id2string(component_name)))
      {
        // Looking for the member overwritten by this WITH expression
        std::string remaining_suffix =
          strip_first_field_from_suffix(suffix, id2string(component_name));
        get_value_set_rec(
          with_expr.new_value(), dest, remaining_suffix, original_type, ns);
      }
      else if(to_struct_type(expr_type).has_component(component_name))
      {
        // Looking for a non-overwritten member, look through this expression
        get_value_set_rec(with_expr.old(), dest, suffix, original_type, ns);
      }
      else
      {
        // Member we're looking for is not defined in this struct -- this
        // must be a reinterpret cast of some sort. Default to conservatively
        // assuming either operand might be involved.
        get_value_set_rec(with_expr.old(), dest, suffix, original_type, ns);
        get_value_set_rec(with_expr.new_value(), dest, "", original_type, ns);
      }
    }
    else if(expr_type.id() == ID_array && !suffix.empty())
    {
      std::string new_value_suffix;
      if(has_prefix(suffix, "[]"))
        new_value_suffix = suffix.substr(2);

      // Otherwise use a blank suffix on the assumption anything involved with
      // the new value might be interesting.

      get_value_set_rec(with_expr.old(), dest, suffix, original_type, ns);
      get_value_set_rec(
        with_expr.new_value(), dest, new_value_suffix, original_type, ns);
    }
    else
    {
      // Something else-- the suffixes used here are a rough guess at best,
      // so this is imprecise.
      get_value_set_rec(with_expr.old(), dest, suffix, original_type, ns);
      get_value_set_rec(with_expr.new_value(), dest, "", original_type, ns);
    }
  }
  else if(expr.id()==ID_array)
  {
    // an array constructor, possibly containing addresses
    std::string new_suffix = suffix;
    if(has_prefix(suffix, "[]"))
      new_suffix = suffix.substr(2);
    // Otherwise we're probably reinterpreting some other type -- try persisting
    // with the current suffix for want of a better idea.

    forall_operands(it, expr)
      get_value_set_rec(*it, dest, new_suffix, original_type, ns);
  }
  else if(expr.id()==ID_array_of)
  {
    // an array constructor, possibly containing an address
    std::string new_suffix = suffix;
    if(has_prefix(suffix, "[]"))
      new_suffix = suffix.substr(2);
    // Otherwise we're probably reinterpreting some other type -- try persisting
    // with the current suffix for want of a better idea.

    get_value_set_rec(
      to_array_of_expr(expr).what(), dest, new_suffix, original_type, ns);
  }
  else if(expr.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(expr);

    const std::string prefix=
      "value_set::dynamic_object"+
      std::to_string(dynamic_object.get_instance());

    // first try with suffix
    const std::string full_name=prefix+suffix;

    // look it up
    const entryt *entry = find_entry(full_name);

    // not found? try without suffix
    if(!entry)
      entry = find_entry(prefix);

    if(!entry)
      insert(dest, exprt(ID_unknown, original_type));
    else
      make_union(dest, entry->object_map);
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    const auto &byte_extract_expr = to_byte_extract_expr(expr);

    bool found=false;

    const typet &op_type = ns.follow(byte_extract_expr.op().type());
    if(op_type.id() == ID_struct)
    {
      exprt offset = byte_extract_expr.offset();
      if(eval_pointer_offset(offset, ns))
        simplify(offset, ns);

      const auto offset_int = numeric_cast<mp_integer>(offset);
      const auto type_size = pointer_offset_size(expr.type(), ns);

      const struct_typet &struct_type = to_struct_type(op_type);

      for(const auto &c : struct_type.components())
      {
        const irep_idt &name = c.get_name();

        if(offset_int.has_value())
        {
          auto comp_offset = member_offset(struct_type, name, ns);
          if(comp_offset.has_value())
          {
            if(
              type_size.has_value() && *offset_int + *type_size <= *comp_offset)
            {
              break;
            }

            auto member_size = pointer_offset_size(c.type(), ns);
            if(
              member_size.has_value() &&
              *offset_int >= *comp_offset + *member_size)
            {
              continue;
            }
          }
        }

        found=true;

        member_exprt member(byte_extract_expr.op(), c);
        get_value_set_rec(member, dest, suffix, original_type, ns);
      }
    }

    if(op_type.id() == ID_union)
    {
      // just collect them all
      for(const auto &c : to_union_type(op_type).components())
      {
        const irep_idt &name = c.get_name();
        member_exprt member(byte_extract_expr.op(), name, c.type());
        get_value_set_rec(member, dest, suffix, original_type, ns);
      }
    }

    if(!found)
      // we just pass through
      get_value_set_rec(
        byte_extract_expr.op(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    const auto &byte_update_expr = to_byte_update_expr(expr);

    // we just pass through
    get_value_set_rec(byte_update_expr.op(), dest, suffix, original_type, ns);
    get_value_set_rec(
      byte_update_expr.value(), dest, suffix, original_type, ns);

    // we could have checked object size to be more precise
  }
  else if(expr.id() == ID_let)
  {
    const auto &let_expr = to_let_expr(expr);
    // This depends on copying `value_sett` being cheap -- which it is, because
    // our backing store is sharing_mapt.
    value_sett value_set_with_local_definition = *this;
    value_set_with_local_definition.assign(
      let_expr.symbol(), let_expr.value(), ns, false, false);

    value_set_with_local_definition.get_value_set_rec(
      let_expr.where(), dest, suffix, original_type, ns);
  }
  else
  {
    insert(dest, exprt(ID_unknown, original_type));
  }

  #ifdef DEBUG
  std::cout << "GET_VALUE_SET_REC RESULT:\n";
  for(const auto &obj : dest.read())
  {
    const exprt &e=to_expr(obj);
    std::cout << "  " << format(e) << "\n";
  }
  std::cout << "\n";
  #endif
}

void value_sett::dereference_rec(
  const exprt &src,
  exprt &dest) const
{
  // remove pointer typecasts
  if(src.id()==ID_typecast)
  {
    assert(src.type().id()==ID_pointer);

    dereference_rec(to_typecast_expr(src).op(), dest);
  }
  else
    dest=src;
}

void value_sett::get_reference_set(
  const exprt &expr,
  value_setst::valuest &dest,
  const namespacet &ns) const
{
  object_mapt object_map;
  get_reference_set(expr, object_map, ns);

  for(object_map_dt::const_iterator
      it=object_map.read().begin();
      it!=object_map.read().end();
      it++)
    dest.push_back(to_expr(*it));
}

void value_sett::get_reference_set_rec(
  const exprt &expr,
  object_mapt &dest,
  const namespacet &ns) const
{
#ifdef DEBUG
  std::cout << "GET_REFERENCE_SET_REC EXPR: " << format(expr)
            << '\n';
#endif

  if(expr.id()==ID_symbol ||
     expr.id()==ID_dynamic_object ||
     expr.id()==ID_string_constant ||
     expr.id()==ID_array)
  {
    if(
      expr.type().id() == ID_array &&
      to_array_type(expr.type()).element_type().id() == ID_array)
      insert(dest, expr);
    else
      insert(dest, expr, 0);

    return;
  }
  else if(expr.id()==ID_dereference)
  {
    const auto &pointer = to_dereference_expr(expr).pointer();

    get_value_set_rec(pointer, dest, "", pointer.type(), ns);

#ifdef DEBUG
    for(const auto &map_entry : dest.read())
    {
      std::cout << "VALUE_SET: " << format(object_numbering[map_entry.first])
                << '\n';
    }
#endif

    return;
  }
  else if(expr.id()==ID_index)
  {
    if(expr.operands().size()!=2)
      throw "index expected to have two operands";

    const index_exprt &index_expr=to_index_expr(expr);
    const exprt &array=index_expr.array();
    const exprt &offset=index_expr.index();

    DATA_INVARIANT(
      array.type().id() == ID_array, "index takes array-typed operand");

    const auto &array_type = to_array_type(array.type());

    object_mapt array_references;
    get_reference_set(array, array_references, ns);

    const object_map_dt &object_map=array_references.read();

    for(object_map_dt::const_iterator
        a_it=object_map.begin();
        a_it!=object_map.end();
        a_it++)
    {
      const exprt &object=object_numbering[a_it->first];

      if(object.id()==ID_unknown)
        insert(dest, exprt(ID_unknown, expr.type()));
      else
      {
        const index_exprt deref_index_expr(
          typecast_exprt::conditional_cast(object, array_type),
          from_integer(0, c_index_type()));

        offsett o = a_it->second;
        const auto i = numeric_cast<mp_integer>(offset);

        if(offset.is_zero())
        {
        }
        else if(i.has_value() && o)
        {
          auto size = pointer_offset_size(array_type.element_type(), ns);

          if(!size.has_value() || *size == 0)
            o.reset();
          else
            *o = *i * (*size);
        }
        else
          o.reset();

        insert(dest, deref_index_expr, o);
      }
    }

    return;
  }
  else if(expr.id()==ID_member)
  {
    const irep_idt &component_name=expr.get(ID_component_name);

    const exprt &struct_op = to_member_expr(expr).compound();

    object_mapt struct_references;
    get_reference_set(struct_op, struct_references, ns);

    const object_map_dt &object_map=struct_references.read();

    for(object_map_dt::const_iterator
        it=object_map.begin();
        it!=object_map.end();
        it++)
    {
      const exprt &object=object_numbering[it->first];

      if(object.id()==ID_unknown)
        insert(dest, exprt(ID_unknown, expr.type()));
      else
      {
        offsett o = it->second;

        member_exprt member_expr(object, component_name, expr.type());

        // We cannot introduce a cast from scalar to non-scalar,
        // thus, we can only adjust the types of structs and unions.

        const typet &final_object_type = ns.follow(object.type());

        if(final_object_type.id()==ID_struct ||
           final_object_type.id()==ID_union)
        {
          // adjust type?
          if(ns.follow(struct_op.type())!=final_object_type)
          {
            member_expr.compound() =
              typecast_exprt(member_expr.compound(), struct_op.type());
          }

          insert(dest, member_expr, o);
        }
        else
          insert(dest, exprt(ID_unknown, expr.type()));
      }
    }

    return;
  }
  else if(expr.id()==ID_if)
  {
    get_reference_set_rec(to_if_expr(expr).true_case(), dest, ns);
    get_reference_set_rec(to_if_expr(expr).false_case(), dest, ns);
    return;
  }

  insert(dest, exprt(ID_unknown, expr.type()));
}

void value_sett::assign(
  const exprt &lhs,
  const exprt &rhs,
  const namespacet &ns,
  bool is_simplified,
  bool add_to_sets)
{
#ifdef DEBUG
  std::cout << "ASSIGN LHS: " << format(lhs) << " : "
            << format(lhs.type()) << '\n';
  std::cout << "ASSIGN RHS: " << format(rhs) << " : "
            << format(rhs.type()) << '\n';
  std::cout << "--------------------------------------------\n";
  output(std::cout);
#endif

  const typet &type=ns.follow(lhs.type());

  if(type.id() == ID_struct)
  {
    for(const auto &c : to_struct_type(type).components())
    {
      const typet &subtype = c.type();
      const irep_idt &name = c.get_name();

      // ignore methods and padding
      if(subtype.id() == ID_code || c.get_is_padding())
        continue;

      member_exprt lhs_member(lhs, name, subtype);

      exprt rhs_member;

      if(rhs.id()==ID_unknown ||
         rhs.id()==ID_invalid)
      {
        // this branch is deemed dead as otherwise we'd be missing assignments
        // that never happened in this branch
        UNREACHABLE;
        rhs_member=exprt(rhs.id(), subtype);
      }
      else
      {
        DATA_INVARIANT(
          rhs.type() == lhs.type(),
          "value_sett::assign types should match, got: "
          "rhs.type():\n" +
            rhs.type().pretty() + "\n" + "lhs.type():\n" + lhs.type().pretty());

        const typet &followed = ns.follow(rhs.type());

        if(followed.id() == ID_struct || followed.id() == ID_union)
        {
          const struct_union_typet &rhs_struct_union_type =
            to_struct_union_type(followed);

          const typet &rhs_subtype = rhs_struct_union_type.component_type(name);
          rhs_member = simplify_expr(member_exprt{rhs, name, rhs_subtype}, ns);

          assign(lhs_member, rhs_member, ns, true, add_to_sets);
        }
      }
    }
  }
  else if(type.id()==ID_array)
  {
    const index_exprt lhs_index(
      lhs,
      exprt(ID_unknown, c_index_type()),
      to_array_type(type).element_type());

    if(rhs.id()==ID_unknown ||
       rhs.id()==ID_invalid)
    {
      assign(
        lhs_index,
        exprt(rhs.id(), to_array_type(type).element_type()),
        ns,
        is_simplified,
        add_to_sets);
    }
    else
    {
      DATA_INVARIANT(
        rhs.type() == type,
        "value_sett::assign types should match, got: "
        "rhs.type():\n" +
          rhs.type().pretty() + "\n" + "type:\n" + type.pretty());

      if(rhs.id()==ID_array_of)
      {
        assign(
          lhs_index,
          to_array_of_expr(rhs).what(),
          ns,
          is_simplified,
          add_to_sets);
      }
      else if(rhs.id()==ID_array ||
              rhs.id()==ID_constant)
      {
        forall_operands(o_it, rhs)
        {
          assign(lhs_index, *o_it, ns, is_simplified, add_to_sets);
          add_to_sets=true;
        }
      }
      else if(rhs.id()==ID_with)
      {
        const index_exprt op0_index(
          to_with_expr(rhs).old(),
          exprt(ID_unknown, c_index_type()),
          to_array_type(type).element_type());

        assign(lhs_index, op0_index, ns, is_simplified, add_to_sets);
        assign(
          lhs_index, to_with_expr(rhs).new_value(), ns, is_simplified, true);
      }
      else
      {
        const index_exprt rhs_index(
          rhs,
          exprt(ID_unknown, c_index_type()),
          to_array_type(type).element_type());
        assign(lhs_index, rhs_index, ns, is_simplified, true);
      }
    }
  }
  else
  {
    // basic type or union
    object_mapt values_rhs = get_value_set(rhs, ns, is_simplified);

    // Permit custom subclass to alter the read values prior to write:
    adjust_assign_rhs_values(rhs, ns, values_rhs);

    // Permit custom subclass to perform global side-effects prior to write:
    apply_assign_side_effects(lhs, rhs, ns);

    assign_rec(lhs, values_rhs, "", ns, add_to_sets);
  }
}

void value_sett::assign_rec(
  const exprt &lhs,
  const object_mapt &values_rhs,
  const std::string &suffix,
  const namespacet &ns,
  bool add_to_sets)
{
#ifdef DEBUG
  std::cout << "ASSIGN_REC LHS: " << format(lhs) << '\n';
  std::cout << "ASSIGN_REC LHS ID: " << lhs.id() << '\n';
  std::cout << "ASSIGN_REC SUFFIX: " << suffix << '\n';

  for(object_map_dt::const_iterator it=values_rhs.read().begin();
      it!=values_rhs.read().end();
      it++)
    std::cout << "ASSIGN_REC RHS: " <<
      format(object_numbering[it->first]) << '\n';
  std::cout << '\n';
#endif

  if(lhs.id()==ID_symbol)
  {
    const irep_idt &identifier=to_symbol_expr(lhs).get_identifier();

    update_entry(
      entryt{identifier, suffix}, lhs.type(), values_rhs, add_to_sets);
  }
  else if(lhs.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(lhs);

    const std::string name=
      "value_set::dynamic_object"+
      std::to_string(dynamic_object.get_instance());

    update_entry(entryt{name, suffix}, lhs.type(), values_rhs, true);
  }
  else if(lhs.id()==ID_dereference)
  {
    if(lhs.operands().size()!=1)
      throw lhs.id_string()+" expected to have one operand";

    object_mapt reference_set;
    get_reference_set(lhs, reference_set, ns);

    if(reference_set.read().size()!=1)
      add_to_sets=true;

    for(object_map_dt::const_iterator
        it=reference_set.read().begin();
        it!=reference_set.read().end();
        it++)
    {
      /// Do not take a reference to object_numbering's storage as we may call
      /// object_numbering.number(), which may reallocate it.
      const exprt object=object_numbering[it->first];

      if(object.id()!=ID_unknown)
        assign_rec(object, values_rhs, suffix, ns, add_to_sets);
    }
  }
  else if(lhs.id()==ID_index)
  {
    const auto &array = to_index_expr(lhs).array();

    const typet &type = array.type();

    DATA_INVARIANT(
      type.id() == ID_array, "operand 0 of index expression must be an array");

    assign_rec(array, values_rhs, "[]" + suffix, ns, true);
  }
  else if(lhs.id()==ID_member)
  {
    const auto &lhs_member_expr = to_member_expr(lhs);
    const auto &component_name = lhs_member_expr.get_component_name();

    const typet &type = ns.follow(lhs_member_expr.compound().type());

    DATA_INVARIANT(
      type.id() == ID_struct || type.id() == ID_union,
      "operand 0 of member expression must be struct or union");

    assign_rec(
      lhs_member_expr.compound(),
      values_rhs,
      "." + id2string(component_name) + suffix,
      ns,
      add_to_sets);
  }
  else if(lhs.id()=="valid_object" ||
          lhs.id()=="dynamic_type" ||
          lhs.id()=="is_zero_string" ||
          lhs.id()=="zero_string" ||
          lhs.id()=="zero_string_length")
  {
    // we ignore this here
  }
  else if(lhs.id()==ID_string_constant)
  {
    // someone writes into a string-constant
    // evil guy
  }
  else if(lhs.id() == ID_null_object)
  {
    // evil as well
  }
  else if(lhs.id()==ID_typecast)
  {
    const typecast_exprt &typecast_expr=to_typecast_expr(lhs);

    assign_rec(typecast_expr.op(), values_rhs, suffix, ns, add_to_sets);
  }
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
  {
    assign_rec(to_byte_extract_expr(lhs).op(), values_rhs, suffix, ns, true);
  }
  else if(lhs.id()==ID_integer_address)
  {
    // that's like assigning into __CPROVER_memory[...],
    // which we don't track
  }
  else
    throw "assign NYI: '" + lhs.id_string() + "'";
}

void value_sett::do_function_call(
  const irep_idt &function,
  const exprt::operandst &arguments,
  const namespacet &ns)
{
  const symbolt &symbol=ns.lookup(function);

  const code_typet &type=to_code_type(symbol.type);
  const code_typet::parameterst &parameter_types=type.parameters();

  // these first need to be assigned to dummy, temporary arguments
  // and only thereafter to the actuals, in order
  // to avoid overwriting actuals that are needed for recursive
  // calls

  for(std::size_t i=0; i<arguments.size(); i++)
  {
    const std::string identifier="value_set::dummy_arg_"+std::to_string(i);
    const symbol_exprt dummy_lhs(identifier, arguments[i].type());
    assign(dummy_lhs, arguments[i], ns, false, false);
  }

  // now assign to 'actual actuals'

  unsigned i=0;

  for(code_typet::parameterst::const_iterator
      it=parameter_types.begin();
      it!=parameter_types.end();
      it++)
  {
    const irep_idt &identifier=it->get_identifier();
    if(identifier.empty())
      continue;

    const exprt v_expr=
      symbol_exprt("value_set::dummy_arg_"+std::to_string(i), it->type());

    const symbol_exprt actual_lhs(identifier, it->type());
    assign(actual_lhs, v_expr, ns, true, true);
    i++;
  }

  // we could delete the dummy_arg_* now.
}

void value_sett::do_end_function(
  const exprt &lhs,
  const namespacet &ns)
{
  if(lhs.is_nil())
    return;

  symbol_exprt rhs("value_set::return_value", lhs.type());

  assign(lhs, rhs, ns, false, false);
}

void value_sett::apply_code_rec(
  const codet &code,
  const namespacet &ns)
{
  const irep_idt &statement=code.get_statement();

  if(statement==ID_block)
  {
    forall_operands(it, code)
      apply_code_rec(to_code(*it), ns);
  }
  else if(statement==ID_function_call)
  {
    // shouldn't be here
    UNREACHABLE;
  }
  else if(statement==ID_assign)
  {
    if(code.operands().size()!=2)
      throw "assignment expected to have two operands";

    assign(code.op0(), code.op1(), ns, false, false);
  }
  else if(statement==ID_decl)
  {
    if(code.operands().size()!=1)
      throw "decl expected to have one operand";

    const exprt &lhs=code.op0();

    if(lhs.id()!=ID_symbol)
      throw "decl expected to have symbol on lhs";

    const typet &lhs_type = lhs.type();

    if(
      lhs_type.id() == ID_pointer ||
      (lhs_type.id() == ID_array &&
       to_array_type(lhs_type).element_type().id() == ID_pointer))
    {
      // assign the address of the failed object
      if(auto failed = get_failed_symbol(to_symbol_expr(lhs), ns))
      {
        address_of_exprt address_of_expr(*failed, to_pointer_type(lhs.type()));
        assign(lhs, address_of_expr, ns, false, false);
      }
      else
        assign(lhs, exprt(ID_invalid), ns, false, false);
    }
  }
  else if(statement==ID_expression)
  {
    // can be ignored, we don't expect side effects here
  }
  else if(statement == ID_cpp_delete || statement == ID_cpp_delete_array)
  {
    // does nothing
  }
  else if(statement=="lock" || statement=="unlock")
  {
    // ignore for now
  }
  else if(statement==ID_asm)
  {
    // ignore for now, probably not safe
  }
  else if(statement==ID_nondet)
  {
    // doesn't do anything
  }
  else if(statement==ID_printf)
  {
    // doesn't do anything
  }
  else if(statement==ID_return)
  {
    const code_returnt &code_return = to_code_return(code);
    // this is turned into an assignment
    symbol_exprt lhs(
      "value_set::return_value", code_return.return_value().type());
    assign(lhs, code_return.return_value(), ns, false, false);
  }
  else if(statement==ID_array_set)
  {
  }
  else if(statement==ID_array_copy)
  {
  }
  else if(statement==ID_array_replace)
  {
  }
  else if(statement == ID_array_equal)
  {
  }
  else if(statement==ID_assume)
  {
    guard(to_code_assume(code).assumption(), ns);
  }
  else if(statement==ID_user_specified_predicate ||
          statement==ID_user_specified_parameter_predicates ||
          statement==ID_user_specified_return_predicates)
  {
    // doesn't do anything
  }
  else if(statement==ID_fence)
  {
  }
  else if(can_cast_expr<code_inputt>(code) || can_cast_expr<code_outputt>(code))
  {
    // doesn't do anything
  }
  else if(statement==ID_dead)
  {
    // Ignore by default; could prune the value set.
  }
  else
  {
    // std::cerr << code.pretty() << '\n';
    throw "value_sett: unexpected statement: "+id2string(statement);
  }
}

void value_sett::guard(
  const exprt &expr,
  const namespacet &ns)
{
  if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      guard(*it, ns);
  }
  else if(expr.id()==ID_equal)
  {
  }
  else if(expr.id()==ID_notequal)
  {
  }
  else if(expr.id()==ID_not)
  {
  }
  else if(expr.id()==ID_dynamic_object)
  {
    dynamic_object_exprt dynamic_object(unsigned_char_type());
    // dynamic_object.instance()=
    // from_integer(location_number, typet(ID_natural));
    dynamic_object.valid()=true_exprt();

    address_of_exprt address_of(dynamic_object);
    address_of.type() = to_dynamic_object_expr(expr).op0().type();

    assign(to_dynamic_object_expr(expr).op0(), address_of, ns, false, false);
  }
}

void value_sett::erase_values_from_entry(
  const irep_idt &index,
  const std::unordered_set<exprt, irep_hash> &values_to_erase)
{
  if(values_to_erase.empty())
    return;

  auto entry = find_entry(index);
  if(!entry)
    return;

  std::vector<object_map_dt::key_type> keys_to_erase;

  for(auto &key_value : entry->object_map.read())
  {
    const auto &rhs_object = to_expr(key_value);
    if(values_to_erase.count(rhs_object))
    {
      keys_to_erase.emplace_back(key_value.first);
    }
  }

  DATA_INVARIANT(
    keys_to_erase.size() == values_to_erase.size(),
    "value_sett::erase_value_from_entry() should erase exactly one value for "
    "each element in the set it is given");

  entryt replacement = *entry;
  for(const auto &key_to_erase : keys_to_erase)
  {
    replacement.object_map.write().erase(key_to_erase);
  }
  values.replace(index, std::move(replacement));
}

void value_sett::erase_struct_union_symbol(
  const struct_union_typet &struct_union_type,
  const std::string &erase_prefix,
  const namespacet &ns)
{
  for(const auto &c : struct_union_type.components())
  {
    const typet &subtype = c.type();
    const irep_idt &name = c.get_name();

    // ignore methods and padding
    if(subtype.id() == ID_code || c.get_is_padding())
      continue;

    erase_symbol_rec(subtype, erase_prefix + "." + id2string(name), ns);
  }
}

void value_sett::erase_symbol_rec(
  const typet &type,
  const std::string &erase_prefix,
  const namespacet &ns)
{
  if(type.id() == ID_struct_tag)
    erase_struct_union_symbol(
      ns.follow_tag(to_struct_tag_type(type)), erase_prefix, ns);
  else if(type.id() == ID_union_tag)
    erase_struct_union_symbol(
      ns.follow_tag(to_union_tag_type(type)), erase_prefix, ns);
  else if(type.id() == ID_array)
    erase_symbol_rec(
      to_array_type(type).element_type(), erase_prefix + "[]", ns);
  else if(values.has_key(erase_prefix))
    values.erase(erase_prefix);
}

void value_sett::erase_symbol(
  const symbol_exprt &symbol_expr,
  const namespacet &ns)
{
  erase_symbol_rec(
    symbol_expr.type(), id2string(symbol_expr.get_identifier()), ns);
}
