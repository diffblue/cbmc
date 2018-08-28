/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Value Set

#include "value_set.h"

#include <cassert>
#include <ostream>

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/c_types.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

#include <langapi/language_util.h>

#ifdef DEBUG
#include <iostream>
#include <util/format_expr.h>
#include <util/format_type.h>
#endif

#include "add_failed_symbols.h"

// Due to a large number of functions defined inline, `value_sett` and
// associated types are documented in its header file, `value_set.h`.

const value_sett::object_map_dt value_sett::object_map_dt::blank{};
object_numberingt value_sett::object_numbering;

bool value_sett::field_sensitive(
  const irep_idt &id,
  const typet &type,
  const namespacet &ns)
{
  // we always track fields on these
  if(has_prefix(id2string(id), "value_set::dynamic_object") ||
     id=="value_set::return_value" ||
     id=="value_set::memory")
    return true;

  // otherwise it has to be a struct
  return ns.follow(type).id()==ID_struct;
}

value_sett::entryt &value_sett::get_entry(
  const entryt &e,
  const typet &type,
  const namespacet &ns)
{
  irep_idt index;

  if(field_sensitive(e.identifier, type, ns))
    index=id2string(e.identifier)+e.suffix;
  else
    index=e.identifier;

  std::pair<valuest::iterator, bool> r=
    values.insert(std::pair<idt, entryt>(index, e));

  return r.first->second;
}

bool value_sett::insert(
  object_mapt &dest,
  object_numberingt::number_type n,
  const offsett &offset) const
{
  auto entry=dest.read().find(n);

  if(entry==dest.read().end())
  {
    // new
    dest.write()[n] = offset;
    return true;
  }
  else if(!entry->second)
    return false; // no change
  else if(offset && *entry->second == *offset)
    return false; // no change
  else
  {
    dest.write()[n].reset();
    return true;
  }
}

void value_sett::output(
  const namespacet &ns,
  std::ostream &out) const
{
  for(valuest::const_iterator
      v_it=values.begin();
      v_it!=values.end();
      v_it++)
  {
    irep_idt identifier, display_name;

    const entryt &e=v_it->second;

    if(has_prefix(id2string(e.identifier), "value_set::dynamic_object"))
    {
      display_name=id2string(e.identifier)+e.suffix;
      identifier="";
    }
    else if(e.identifier=="value_set::return_value")
    {
      display_name="RETURN_VALUE"+e.suffix;
      identifier="";
    }
    else
    {
      #if 0
      const symbolt &symbol=ns.lookup(e.identifier);
      display_name=id2string(symbol.display_name())+e.suffix;
      identifier=symbol.name;
      #else
      identifier=id2string(e.identifier);
      display_name=id2string(identifier)+e.suffix;
      #endif
    }

    out << display_name;

    out << " = { ";

    const object_map_dt &object_map=e.object_map.read();

    std::size_t width=0;

    for(object_map_dt::const_iterator
        o_it=object_map.begin();
        o_it!=object_map.end();
        o_it++)
    {
      const exprt &o=object_numbering[o_it->first];

      std::string result;

      if(o.id()==ID_invalid || o.id()==ID_unknown)
        result=from_expr(ns, identifier, o);
      else
      {
        result="<"+from_expr(ns, identifier, o)+", ";

        if(o_it->second)
          result += integer2string(*o_it->second) + "";
        else
          result+='*';

        if(o.type().is_nil())
          result+=", ?";
        else
          result+=", "+from_type(ns, identifier, o.type());

        result+='>';
      }

      out << result;

      width+=result.size();

      object_map_dt::const_iterator next(o_it);
      next++;

      if(next!=object_map.end())
      {
        out << ", ";
        if(width>=40)
          out << "\n      ";
      }
    }

    out << " } \n";
  }
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
    od.offset() = from_integer(*it.second, index_type());

  od.type()=od.object().type();

  return od;
}

bool value_sett::make_union(const value_sett::valuest &new_values)
{
  bool result=false;

  valuest::iterator v_it=values.begin();

  for(valuest::const_iterator
      it=new_values.begin();
      it!=new_values.end();
      ) // no it++
  {
    if(v_it==values.end() || it->first<v_it->first)
    {
      values.insert(v_it, *it);
      result=true;
      it++;
      continue;
    }
    else if(v_it->first<it->first)
    {
      v_it++;
      continue;
    }

    assert(v_it->first==it->first);

    entryt &e=v_it->second;
    const entryt &new_e=it->second;

    if(make_union(e.object_map, new_e.object_map))
      result=true;

    v_it++;
    it++;
  }

  return result;
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
    assert(expr.operands().size()==1);

    object_mapt reference_set;
    get_value_set(expr.op0(), reference_set, ns, true);

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
        mp_integer ptr_offset=compute_pointer_offset(object, ns);

        if(ptr_offset<0)
          return false;

        ptr_offset += *it->second;

        if(mod && ptr_offset!=previous_offset)
          return false;

        new_expr=from_integer(ptr_offset, expr.type());
        previous_offset=ptr_offset;
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

void value_sett::get_value_set(
  const exprt &expr,
  value_setst::valuest &dest,
  const namespacet &ns) const
{
  object_mapt object_map;
  get_value_set(expr, object_map, ns, false);

  for(object_map_dt::const_iterator
      it=object_map.read().begin();
      it!=object_map.read().end();
      it++)
    dest.push_back(to_expr(*it));

  #if 0
  for(value_setst::valuest::const_iterator it=dest.begin();
      it!=dest.end(); it++)
    std::cout << "GET_VALUE_SET: " << format(*it) << '\n';
  #endif
}

void value_sett::get_value_set(
  const exprt &expr,
  object_mapt &dest,
  const namespacet &ns,
  bool is_simplified) const
{
  exprt tmp(expr);
  if(!is_simplified)
    simplify(tmp, ns);

  get_value_set_rec(tmp, dest, "", tmp.type(), ns);
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

void value_sett::get_value_set_rec(
  const exprt &expr,
  object_mapt &dest,
  const std::string &suffix,
  const typet &original_type,
  const namespacet &ns) const
{
  #if 0
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
    assert(expr.operands().size()==2);

    const typet &type=ns.follow(expr.op0().type());

    DATA_INVARIANT(type.id()==ID_array ||
                   type.id()==ID_incomplete_array,
                   "operand 0 of index expression must be an array");

    get_value_set_rec(expr.op0(), dest, "[]"+suffix, original_type, ns);
  }
  else if(expr.id()==ID_member)
  {
    assert(expr.operands().size()==1);

    const typet &type=ns.follow(expr.op0().type());

    DATA_INVARIANT(type.id()==ID_struct ||
                   type.id()==ID_union ||
                   type.id()==ID_incomplete_struct ||
                   type.id()==ID_incomplete_union,
                   "operand 0 of member expression must be struct or union");

    const std::string &component_name=
      expr.get_string(ID_component_name);

    get_value_set_rec(expr.op0(), dest,
      "."+component_name+suffix, original_type, ns);
  }
  else if(expr.id()==ID_symbol)
  {
    irep_idt identifier=to_symbol_expr(expr).get_identifier();

    // is it a pointer, integer, array or struct?
    if(expr_type.id()==ID_pointer ||
       expr_type.id()==ID_signedbv ||
       expr_type.id()==ID_unsignedbv ||
       expr_type.id()==ID_struct ||
       expr_type.id()==ID_union ||
       expr_type.id()==ID_array)
    {
      // look it up
      valuest::const_iterator v_it=
        values.find(id2string(identifier)+suffix);

      // try first component name as suffix if not yet found
      if(v_it==values.end() &&
          (expr_type.id()==ID_struct ||
           expr_type.id()==ID_union))
      {
        const struct_union_typet &struct_union_type=
          to_struct_union_type(expr_type);

        const std::string first_component_name=
          struct_union_type.components().front().get_string(ID_name);

        v_it=values.find(
            id2string(identifier)+"."+first_component_name+suffix);
      }

      // not found? try without suffix
      if(v_it==values.end())
        v_it=values.find(identifier);

      if(v_it!=values.end())
        make_union(dest, v_it->second.object_map);
      else
        insert(dest, exprt(ID_unknown, original_type));
    }
    else
      insert(dest, exprt(ID_unknown, original_type));
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()!=3)
      throw "if takes three operands";

    get_value_set_rec(expr.op1(), dest, suffix, original_type, ns);
    get_value_set_rec(expr.op2(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_address_of)
  {
    if(expr.operands().size()!=1)
      throw expr.id_string()+" expected to have one operand";

    get_reference_set(expr.op0(), dest, ns);
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
  else if(expr.id()=="reference_to")
  {
    // old stuff, will go away
    object_mapt reference_set;

    get_reference_set(expr, reference_set, ns);

    const object_map_dt &object_map=reference_set.read();

    if(object_map.begin()==object_map.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
    {
      for(object_map_dt::const_iterator
          it=object_map.begin();
          it!=object_map.end();
          it++)
      {
        /// Do not take a reference to object_numbering's storage as we may call
        /// object_numbering.number(), which may reallocate it.
        const exprt object=object_numbering[it->first];
        get_value_set_rec(object, dest, suffix, original_type, ns);
      }
    }
  }
  else if(expr.is_constant())
  {
    // check if NULL
    if(expr.get(ID_value)==ID_NULL &&
       expr_type.id()==ID_pointer)
    {
      insert(dest, exprt(ID_null_object, expr_type.subtype()), 0);
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
    if(expr.operands().size()!=1)
      throw "typecast takes one operand";

    // let's see what gets converted to what

    const typet &op_type=ns.follow(expr.op0().type());

    if(op_type.id()==ID_pointer)
    {
      // pointer-to-pointer -- we just ignore these
      get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
    }
    else if(op_type.id()==ID_unsignedbv ||
            op_type.id()==ID_signedbv)
    {
      // integer-to-pointer

      if(expr.op0().is_zero())
        insert(dest, exprt(ID_null_object, expr_type.subtype()), 0);
      else
      {
        // see if we have something for the integer
        object_mapt tmp;

        get_value_set_rec(expr.op0(), tmp, suffix, original_type, ns);

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
  else if(expr.id()==ID_plus ||
          expr.id()==ID_minus)
  {
    if(expr.operands().size()<2)
      throw expr.id_string()+" expected to have at least two operands";

    object_mapt pointer_expr_set;
    mp_integer i;
    bool i_is_set=false;

    // special case for pointer+integer

    if(expr.operands().size()==2 &&
       expr_type.id()==ID_pointer)
    {
      exprt ptr_operand;

      if(expr.op0().type().id()!=ID_pointer &&
         expr.op0().is_constant())
      {
        i_is_set=!to_integer(expr.op0(), i);
        ptr_operand=expr.op1();
      }
      else
      {
        i_is_set=!to_integer(expr.op1(), i);
        ptr_operand=expr.op0();
      }

      if(i_is_set)
      {
        typet pointer_sub_type=ptr_operand.type().subtype();
        if(pointer_sub_type.id()==ID_empty)
          pointer_sub_type=char_type();

        mp_integer size=pointer_offset_size(pointer_sub_type, ns);

        if(size<=0)
        {
          i_is_set=false;
        }
        else
        {
          i*=size;

          if(expr.id()==ID_minus)
            i.negate();
        }
      }

      get_value_set_rec(
        ptr_operand, pointer_expr_set, "", ptr_operand.type(), ns);
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
      if(offset && i_is_set)
        *offset += i;
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
    const irep_idt &statement=expr.get(ID_statement);

    if(statement==ID_function_call)
    {
      // these should be gone
      throw "unexpected function_call sideeffect";
    }
    else if(statement==ID_allocate)
    {
      assert(suffix=="");

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
      assert(suffix=="");
      assert(expr_type.id()==ID_pointer);

      dynamic_object_exprt dynamic_object(expr_type.subtype());
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
        get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
        get_value_set_rec(expr.op2(), dest, "", original_type, ns);
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
      get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
      get_value_set_rec(expr.op2(), dest, "", original_type, ns);
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

    assert(expr.operands().size()==1);
    get_value_set_rec(expr.op0(), dest, new_suffix, original_type, ns);
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
    valuest::const_iterator v_it=values.find(full_name);

    // not found? try without suffix
    if(v_it==values.end())
      v_it=values.find(prefix);

    if(v_it==values.end())
      insert(dest, exprt(ID_unknown, original_type));
    else
      make_union(dest, v_it->second.object_map);
  }
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
  {
    if(expr.operands().size()!=2)
      throw "byte_extract takes two operands";

    bool found=false;

    exprt op1=expr.op1();
    if(eval_pointer_offset(op1, ns))
      simplify(op1, ns);

    mp_integer op1_offset;
    const typet &op0_type=ns.follow(expr.op0().type());
    if(!to_integer(op1, op1_offset) && op0_type.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(op0_type);

      for(struct_union_typet::componentst::const_iterator
          c_it=struct_type.components().begin();
          !found && c_it!=struct_type.components().end();
          c_it++)
      {
        const irep_idt &name=c_it->get_name();

        mp_integer comp_offset=member_offset(struct_type, name, ns);

        if(comp_offset>op1_offset)
          break;
        else if(comp_offset!=op1_offset)
          continue;

        found=true;

        member_exprt member(expr.op0(), *c_it);
        get_value_set_rec(member, dest, suffix, original_type, ns);
      }
    }

    if(op0_type.id()==ID_union)
    {
      const union_typet &union_type=to_union_type(op0_type);

      // just collect them all
      for(union_typet::componentst::const_iterator
          c_it=union_type.components().begin();
          c_it!=union_type.components().end(); c_it++)
      {
        const irep_idt &name=c_it->get_name();
        member_exprt member(expr.op0(), name, c_it->type());
        get_value_set_rec(member, dest, suffix, original_type, ns);
      }
    }

    if(!found)
      // we just pass through
      get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    if(expr.operands().size()!=3)
      throw "byte_update takes three operands";

    // we just pass through
    get_value_set_rec(expr.op0(), dest, suffix, original_type, ns);
    get_value_set_rec(expr.op2(), dest, suffix, original_type, ns);

    // we could have checked object size to be more precise
  }
  else
  {
    #if 0
    std::cout << "WARNING: not doing " << expr.id() << '\n';
    #endif
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

    if(src.operands().size()!=1)
      throw "typecast expects one operand";

    dereference_rec(src.op0(), dest);
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
  #if 0
  std::cout << "GET_REFERENCE_SET_REC EXPR: " << format(expr)
            << '\n';
  #endif

  if(expr.id()==ID_symbol ||
     expr.id()==ID_dynamic_object ||
     expr.id()==ID_string_constant ||
     expr.id()==ID_array)
  {
    if(expr.type().id()==ID_array &&
       expr.type().subtype().id()==ID_array)
      insert(dest, expr);
    else
      insert(dest, expr, 0);

    return;
  }
  else if(expr.id()==ID_dereference)
  {
    if(expr.operands().size()!=1)
      throw expr.id_string()+" expected to have one operand";

    get_value_set_rec(expr.op0(), dest, "", expr.op0().type(), ns);

    #if 0
    for(expr_sett::const_iterator it=value_set.begin();
        it!=value_set.end(); it++)
      std::cout << "VALUE_SET: " << format(*it) << '\n';
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
    const typet &array_type=ns.follow(array.type());

    assert(array_type.id()==ID_array ||
           array_type.id()==ID_incomplete_array);

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
        index_exprt index_expr(expr.type());
        index_expr.array()=object;
        index_expr.index()=from_integer(0, index_type());

        // adjust type?
        if(ns.follow(object.type())!=array_type)
          index_expr.make_typecast(array.type());

        offsett o = a_it->second;
        mp_integer i;

        if(offset.is_zero())
        {
        }
        else if(!to_integer(offset, i) && o)
        {
          mp_integer size=pointer_offset_size(array_type.subtype(), ns);

          if(size<=0)
            o.reset();
          else
            *o = i * size;
        }
        else
          o.reset();

        insert(dest, index_expr, o);
      }
    }

    return;
  }
  else if(expr.id()==ID_member)
  {
    const irep_idt &component_name=expr.get(ID_component_name);

    if(expr.operands().size()!=1)
      throw "member expected to have one operand";

    const exprt &struct_op=expr.op0();

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
            member_expr.op0().make_typecast(struct_op.type());

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
    if(expr.operands().size()!=3)
      throw "if takes three operands";

    get_reference_set_rec(expr.op1(), dest, ns);
    get_reference_set_rec(expr.op2(), dest, ns);
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
#if 0
  std::cout << "ASSIGN LHS: " << format(lhs) << " : "
            << format(lhs.type()) << '\n';
  std::cout << "ASSIGN RHS: " << format(rhs) << " : "
            << format(rhs.type()) << '\n';
  std::cout << "--------------------------------------------\n";
  output(ns, std::cout);
#endif

  const typet &type=ns.follow(lhs.type());

  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    const struct_union_typet &struct_union_type=
      to_struct_union_type(type);

    for(struct_union_typet::componentst::const_iterator
        c_it=struct_union_type.components().begin();
        c_it!=struct_union_type.components().end();
        c_it++)
    {
      const typet &subtype=c_it->type();
      const irep_idt &name=c_it->get(ID_name);

      // ignore methods and padding
      if(subtype.id()==ID_code ||
         c_it->get_is_padding()) continue;

      member_exprt lhs_member(lhs, name, subtype);

      exprt rhs_member;

      if(rhs.id()==ID_unknown ||
         rhs.id()==ID_invalid)
      {
        rhs_member=exprt(rhs.id(), subtype);
      }
      else
      {
        if(!base_type_eq(rhs.type(), type, ns))
          throw "value_sett::assign type mismatch: "
                "rhs.type():\n"+rhs.type().pretty()+"\n"+
                "type:\n"+type.pretty();

        rhs_member=make_member(rhs, name, ns);

        assign(lhs_member, rhs_member, ns, false, add_to_sets);
      }
    }
  }
  else if(type.id()==ID_array)
  {
    const index_exprt lhs_index(
      lhs, exprt(ID_unknown, index_type()), type.subtype());

    if(rhs.id()==ID_unknown ||
       rhs.id()==ID_invalid)
    {
      assign(
        lhs_index,
        exprt(rhs.id(), type.subtype()),
        ns,
        is_simplified,
        add_to_sets);
    }
    else
    {
      if(!base_type_eq(rhs.type(), type, ns))
        throw "value_sett::assign type mismatch: "
          "rhs.type():\n"+rhs.type().pretty()+"\n"+
          "type:\n"+type.pretty();

      if(rhs.id()==ID_array_of)
      {
        assert(rhs.operands().size()==1);
        assign(lhs_index, rhs.op0(), ns, is_simplified, add_to_sets);
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
        assert(rhs.operands().size()==3);

        const index_exprt op0_index(
          rhs.op0(), exprt(ID_unknown, index_type()), type.subtype());

        assign(lhs_index, op0_index, ns, is_simplified, add_to_sets);
        assign(lhs_index, rhs.op2(), ns, is_simplified, true);
      }
      else
      {
        const index_exprt rhs_index(
          rhs, exprt(ID_unknown, index_type()), type.subtype());
        assign(lhs_index, rhs_index, ns, is_simplified, true);
      }
    }
  }
  else
  {
    // basic type
    object_mapt values_rhs;
    get_value_set(rhs, values_rhs, ns, is_simplified);

    // Permit custom subclass to alter the read values prior to write:
    adjust_assign_rhs_values(rhs, ns, values_rhs);

    // Permit custom subclass to perform global side-effects prior to write:
    apply_assign_side_effects(lhs, rhs, ns);

    assign_rec(lhs, values_rhs, "", ns, add_to_sets);
  }
}

void value_sett::do_free(
  const exprt &op,
  const namespacet &ns)
{
  // op must be a pointer
  if(op.type().id()!=ID_pointer)
    throw "free expected to have pointer-type operand";

  // find out what it points to
  object_mapt value_set;
  get_value_set(op, value_set, ns, false);

  const object_map_dt &object_map=value_set.read();

  // find out which *instances* interest us
  dynamic_object_id_sett to_mark;

  for(object_map_dt::const_iterator
      it=object_map.begin();
      it!=object_map.end();
      it++)
  {
    const exprt &object=object_numbering[it->first];

    if(object.id()==ID_dynamic_object)
    {
      const dynamic_object_exprt &dynamic_object=
        to_dynamic_object_expr(object);

      if(dynamic_object.valid().is_true())
        to_mark.insert(dynamic_object.get_instance());
    }
  }

  // mark these as 'may be invalid'
  // this, unfortunately, destroys the sharing
  for(valuest::iterator v_it=values.begin();
      v_it!=values.end();
      v_it++)
  {
    object_mapt new_object_map;

    const object_map_dt &old_object_map=
      v_it->second.object_map.read();

    bool changed=false;

    for(object_map_dt::const_iterator
        o_it=old_object_map.begin();
        o_it!=old_object_map.end();
        o_it++)
    {
      const exprt &object=object_numbering[o_it->first];

      if(object.id()==ID_dynamic_object)
      {
        const dynamic_object_exprt &dynamic_object=
          to_dynamic_object_expr(object);

        if(to_mark.count(dynamic_object.get_instance())==0)
          set(new_object_map, *o_it);
        else
        {
          // adjust
          offsett o = o_it->second;
          exprt tmp(object);
          to_dynamic_object_expr(tmp).valid()=exprt(ID_unknown);
          insert(new_object_map, tmp, o);
          changed=true;
        }
      }
      else
        set(new_object_map, *o_it);
    }

    if(changed)
      v_it->second.object_map=new_object_map;
  }
}

void value_sett::assign_rec(
  const exprt &lhs,
  const object_mapt &values_rhs,
  const std::string &suffix,
  const namespacet &ns,
  bool add_to_sets)
{
  #if 0
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

    entryt &e=get_entry(entryt(identifier, suffix), lhs.type(), ns);

    if(add_to_sets)
      make_union(e.object_map, values_rhs);
    else
      e.object_map=values_rhs;
  }
  else if(lhs.id()==ID_dynamic_object)
  {
    const dynamic_object_exprt &dynamic_object=
      to_dynamic_object_expr(lhs);

    const std::string name=
      "value_set::dynamic_object"+
      std::to_string(dynamic_object.get_instance());

    entryt &e=get_entry(entryt(name, suffix), lhs.type(), ns);

    make_union(e.object_map, values_rhs);
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
    if(lhs.operands().size()!=2)
      throw "index expected to have two operands";

    const typet &type=ns.follow(lhs.op0().type());

    DATA_INVARIANT(type.id()==ID_array || type.id()==ID_incomplete_array,
                   "operand 0 of index expression must be an array");

    assign_rec(lhs.op0(), values_rhs, "[]"+suffix, ns, true);
  }
  else if(lhs.id()==ID_member)
  {
    if(lhs.operands().size()!=1)
      throw "member expected to have one operand";

    const std::string &component_name=lhs.get_string(ID_component_name);

    const typet &type=ns.follow(lhs.op0().type());

    DATA_INVARIANT(type.id()==ID_struct ||
                   type.id()==ID_union ||
                   type.id()==ID_incomplete_struct ||
                   type.id()==ID_incomplete_union,
                   "operand 0 of member expression must be struct or union");

    assign_rec(
      lhs.op0(), values_rhs, "."+component_name+suffix, ns, add_to_sets);
  }
  else if(lhs.id()=="valid_object" ||
          lhs.id()=="dynamic_size" ||
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
    assert(lhs.operands().size()==2);
    assign_rec(lhs.op0(), values_rhs, suffix, ns, true);
  }
  else if(lhs.id()==ID_integer_address)
  {
    // that's like assigning into __CPROVER_memory[...],
    // which we don't track
  }
  else
    throw "assign NYI: `"+lhs.id_string()+"'";
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
    if(identifier=="")
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

    const typet &lhs_type=ns.follow(lhs.type());

    if(lhs_type.id()==ID_pointer ||
       (lhs_type.id()==ID_array &&
        ns.follow(lhs_type.subtype()).id()==ID_pointer))
    {
      // assign the address of the failed object
      exprt failed=get_failed_symbol(to_symbol_expr(lhs), ns);

      if(failed.is_not_nil())
      {
        address_of_exprt address_of_expr(
          failed, to_pointer_type(lhs.type()));
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
  else if(statement=="cpp_delete" ||
          statement=="cpp_delete[]")
  {
    // does nothing
  }
  else if(statement==ID_free)
  {
    // this may kill a valid bit

    if(code.operands().size()!=1)
      throw "free expected to have one operand";

    do_free(code.op0(), ns);
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
    // this is turned into an assignment
    if(code.operands().size()==1)
    {
      symbol_exprt lhs("value_set::return_value", code.op0().type());
      assign(lhs, code.op0(), ns, false, false);
    }
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
  else if(statement==ID_assume)
  {
    guard(to_code_assume(code).op0(), ns);
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
  else if(statement==ID_input || statement==ID_output)
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
    assert(expr.operands().size()==1);

    dynamic_object_exprt dynamic_object(unsigned_char_type());
    // dynamic_object.instance()=
    // from_integer(location_number, typet(ID_natural));
    dynamic_object.valid()=true_exprt();

    address_of_exprt address_of(dynamic_object);
    address_of.type()=expr.op0().type();

    assign(expr.op0(), address_of, ns, false, false);
  }
}

exprt value_sett::make_member(
  const exprt &src,
  const irep_idt &component_name,
  const namespacet &ns)
{
  const struct_union_typet &struct_union_type=
    to_struct_union_type(ns.follow(src.type()));

  if(src.id()==ID_struct ||
     src.id()==ID_constant)
  {
    std::size_t no=struct_union_type.component_number(component_name);
    assert(no<src.operands().size());
    return src.operands()[no];
  }
  else if(src.id()==ID_with)
  {
    assert(src.operands().size()==3);

    // see if op1 is the member we want
    const exprt &member_operand=src.op1();

    if(component_name==member_operand.get(ID_component_name))
      // yes! just take op2
      return src.op2();
    else
      // no! do this recursively
      return make_member(src.op0(), component_name, ns);
  }
  else if(src.id()==ID_typecast)
  {
    // push through typecast
    assert(src.operands().size()==1);
    return make_member(src.op0(), component_name, ns);
  }

  // give up
  const typet &subtype = struct_union_type.component_type(component_name);
  member_exprt member_expr(src, component_name, subtype);

  return member_expr;
}
