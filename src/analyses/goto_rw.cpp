/*******************************************************************\

Module:

Author: Daniel Kroening

Date: April 2010

\*******************************************************************/

#include "goto_rw.h"

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/byte_operators.h>
#include <util/endianness_map.h>
#include <util/expr_util.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/simplify_expr.h>

#include <goto-programs/goto_functions.h>

#include <langapi/language_util.h>
#include <pointer-analysis/goto_program_dereference.h>

#include <memory>

range_domain_baset::~range_domain_baset()
{
}

void range_domaint::output(const namespacet &, std::ostream &out) const
{
  out << "[";
  for(const_iterator itr=begin();
      itr!=end();
      ++itr)
  {
    if(itr!=begin())
      out << ";";
    out << itr->first << ":" << itr->second;
  }
  out << "]";
}

rw_range_sett::~rw_range_sett()
{
  for(rw_range_sett::objectst::iterator it=r_range_set.begin();
      it!=r_range_set.end();
      ++it)
    it->second=nullptr;

  for(rw_range_sett::objectst::iterator it=w_range_set.begin();
      it!=w_range_set.end();
      ++it)
    it->second=nullptr;
}

void rw_range_sett::output(std::ostream &out) const
{
  out << "READ:\n";
  for(const auto &read_object_entry : get_r_set())
  {
    out << "  " << read_object_entry.first;
    read_object_entry.second->output(ns, out);
    out << '\n';
  }

  out << '\n';

  out << "WRITE:\n";
  for(const auto &written_object_entry : get_w_set())
  {
    out << "  " << written_object_entry.first;
    written_object_entry.second->output(ns, out);
    out << '\n';
  }
}

void rw_range_sett::get_objects_complex_real(
  get_modet mode,
  const complex_real_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  get_objects_rec(mode, expr.op(), range_start, size);
}

void rw_range_sett::get_objects_complex_imag(
  get_modet mode,
  const complex_imag_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  const exprt &op = expr.op();

  auto subtype_bits =
    pointer_offset_bits(to_complex_type(op.type()).subtype(), ns);
  CHECK_RETURN(subtype_bits.has_value());

  range_spect sub_size = range_spect::to_range_spect(*subtype_bits);
  CHECK_RETURN(sub_size > range_spect{0});

  range_spect offset =
    (range_start.is_unknown() || expr.id() == ID_complex_real) ? range_spect{0}
                                                               : sub_size;

  get_objects_rec(mode, op, range_start + offset, size);
}

void rw_range_sett::get_objects_if(
  get_modet mode,
  const if_exprt &if_expr,
  const range_spect &range_start,
  const range_spect &size)
{
  if(if_expr.cond().is_false())
    get_objects_rec(mode, if_expr.false_case(), range_start, size);
  else if(if_expr.cond().is_true())
    get_objects_rec(mode, if_expr.true_case(), range_start, size);
  else
  {
    get_objects_rec(get_modet::READ, if_expr.cond());

    get_objects_rec(mode, if_expr.false_case(), range_start, size);
    get_objects_rec(mode, if_expr.true_case(), range_start, size);
  }
}

void rw_range_sett::get_objects_dereference(
  get_modet mode,
  const dereference_exprt &deref,
  const range_spect &,
  const range_spect &)
{
  const exprt &pointer=deref.pointer();
  get_objects_rec(get_modet::READ, pointer);
  if(mode!=get_modet::READ)
    get_objects_rec(mode, pointer);
}

void rw_range_sett::get_objects_byte_extract(
  get_modet mode,
  const byte_extract_exprt &be,
  const range_spect &range_start,
  const range_spect &size)
{
  auto object_size_bits_opt = pointer_offset_bits(be.op().type(), ns);
  const exprt simp_offset=simplify_expr(be.offset(), ns);

  auto index = numeric_cast<bytest>(simp_offset);
  if(
    range_start.is_unknown() || !index.has_value() ||
    !object_size_bits_opt.has_value())
  {
    get_objects_rec(mode, be.op(), range_spect::unknown(), size);
  }
  else
  {
    bitst index_bits = bytes_to_bits(*index, be.get_bits_per_byte());
    if(index_bits >= *object_size_bits_opt)
      return;

    endianness_mapt map(
      be.op().type(),
      be.id()==ID_byte_extract_little_endian,
      ns);
    range_spect offset = range_start;
    if(index_bits > bitst{0})
    {
      offset += range_spect::to_range_spect(
        bitst{map.map_bit(numeric_cast_v<std::size_t>(index_bits))});
    }
    else
    {
      // outside the bounds of immediate byte-extract operand, might still be in
      // bounds of a parent object
      offset += range_spect::to_range_spect(index_bits);
    }
    get_objects_rec(mode, be.op(), offset, size);
  }
}

void rw_range_sett::get_objects_shift(
  get_modet mode,
  const shift_exprt &shift,
  const range_spect &range_start,
  const range_spect &size)
{
  const exprt simp_distance=simplify_expr(shift.distance(), ns);

  auto op_bits = pointer_offset_bits(shift.op().type(), ns);

  range_spect src_size = op_bits.has_value()
                           ? range_spect::to_range_spect(*op_bits)
                           : range_spect::unknown();

  const auto dist = numeric_cast<bitst>(simp_distance);
  if(
    range_start.is_unknown() || size.is_unknown() || src_size.is_unknown() ||
    !dist.has_value())
  {
    get_objects_rec(
      mode, shift.op(), range_spect::unknown(), range_spect::unknown());
    get_objects_rec(
      mode, shift.distance(), range_spect::unknown(), range_spect::unknown());
  }
  else
  {
    const range_spect dist_r = range_spect::to_range_spect(*dist);

    // not sure whether to worry about
    // config.ansi_c.endianness==configt::ansi_ct::IS_LITTLE_ENDIAN
    // right here maybe?

    if(shift.id()==ID_ashr || shift.id()==ID_lshr)
    {
      range_spect sh_range_start=range_start;
      sh_range_start+=dist_r;

      range_spect sh_size=std::min(size, src_size-sh_range_start);

      if(sh_range_start >= range_spect{0} && sh_range_start < src_size)
        get_objects_rec(mode, shift.op(), sh_range_start, sh_size);
    }
    if(src_size >= dist_r)
    {
      range_spect sh_size=std::min(size, src_size-dist_r);

      get_objects_rec(mode, shift.op(), range_start, sh_size);
    }
  }
}

void rw_range_sett::get_objects_member(
  get_modet mode,
  const member_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  const typet &type = expr.struct_op().type();

  if(
    type.id() == ID_union || type.id() == ID_union_tag ||
    range_start.is_unknown())
  {
    get_objects_rec(mode, expr.struct_op(), range_start, size);
    return;
  }

  const struct_typet &struct_type = type.id() == ID_struct
                                      ? to_struct_type(type)
                                      : ns.follow_tag(to_struct_tag_type(type));

  auto offset_bits =
    member_offset_bits(struct_type, expr.get_component_name(), ns);

  range_spect offset = range_spect::unknown();

  if(offset_bits.has_value())
  {
    offset = range_spect::to_range_spect(*offset_bits);
    offset += range_start;
  }

  get_objects_rec(mode, expr.struct_op(), offset, size);
}

void rw_range_sett::get_objects_index(
  get_modet mode,
  const index_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  if(expr.array().id() == ID_null_object)
    return;

  range_spect sub_size = range_spect::unknown();
  const typet &type = expr.array().type();

  if(type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);

    auto subtype_bits = pointer_offset_bits(vector_type.element_type(), ns);

    if(subtype_bits.has_value())
      sub_size = range_spect::to_range_spect(*subtype_bits);
  }
  else if(type.id()==ID_array)
  {
    const array_typet &array_type=to_array_type(type);

    auto subtype_bits = pointer_offset_bits(array_type.element_type(), ns);

    if(subtype_bits.has_value())
      sub_size = range_spect::to_range_spect(*subtype_bits);
  }
  else
    return;

  const exprt simp_index=simplify_expr(expr.index(), ns);

  const auto index = numeric_cast<mp_integer>(simp_index);
  if(!index.has_value())
    get_objects_rec(get_modet::READ, expr.index());

  if(range_start.is_unknown() || sub_size.is_unknown() || !index.has_value())
    get_objects_rec(mode, expr.array(), range_spect::unknown(), size);
  else
  {
    get_objects_rec(
      mode,
      expr.array(),
      range_start + range_spect::to_range_spect(bitst{*index}) * sub_size,
      size);
  }
}

void rw_range_sett::get_objects_array(
  get_modet mode,
  const array_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  const array_typet &array_type = expr.type();

  auto subtype_bits = pointer_offset_bits(array_type.element_type(), ns);

  if(!subtype_bits.has_value())
  {
    for(const auto &op : expr.operands())
      get_objects_rec(mode, op, range_spect{0}, range_spect::unknown());

    return;
  }

  range_spect sub_size = range_spect::to_range_spect(*subtype_bits);

  range_spect offset{0};
  range_spect full_r_s =
    range_start.is_unknown() ? range_spect{0} : range_start;
  range_spect full_r_e =
    size.is_unknown()
      ? sub_size * range_spect::to_range_spect(bitst{expr.operands().size()})
      : full_r_s + size;

  for(const auto &op : expr.operands())
  {
    if(full_r_s<=offset+sub_size && full_r_e>offset)
    {
      range_spect cur_r_s =
        full_r_s <= offset ? range_spect{0} : full_r_s - offset;
      range_spect cur_r_e=
        full_r_e>offset+sub_size ? sub_size : full_r_e-offset;

      get_objects_rec(mode, op, cur_r_s, cur_r_e - cur_r_s);
    }

    offset+=sub_size;
  }
}

void rw_range_sett::get_objects_struct(
  get_modet mode,
  const struct_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  const struct_typet &struct_type =
    expr.type().id() == ID_struct
      ? to_struct_type(expr.type())
      : ns.follow_tag(to_struct_tag_type(expr.type()));

  auto struct_bits = pointer_offset_bits(struct_type, ns);

  range_spect full_size = struct_bits.has_value()
                            ? range_spect::to_range_spect(*struct_bits)
                            : range_spect::unknown();

  range_spect offset = range_spect{0};
  range_spect full_r_s =
    range_start.is_unknown() ? range_spect{0} : range_start;
  range_spect full_r_e = size.is_unknown() || full_size.is_unknown()
                           ? range_spect::unknown()
                           : full_r_s + size;

  for(const auto &op : expr.operands())
  {
    auto it_bits = pointer_offset_bits(op.type(), ns);

    range_spect sub_size = it_bits.has_value()
                             ? range_spect::to_range_spect(*it_bits)
                             : range_spect::unknown();

    if(offset.is_unknown())
    {
      get_objects_rec(mode, op, range_spect{0}, sub_size);
    }
    else if(sub_size.is_unknown())
    {
      if(full_r_e.is_unknown() || full_r_e > offset)
      {
        range_spect cur_r_s =
          full_r_s <= offset ? range_spect{0} : full_r_s - offset;

        get_objects_rec(mode, op, cur_r_s, range_spect::unknown());
      }

      offset = range_spect::unknown();
    }
    else if(full_r_e.is_unknown())
    {
      if(full_r_s<=offset+sub_size)
      {
        range_spect cur_r_s =
          full_r_s <= offset ? range_spect{0} : full_r_s - offset;

        get_objects_rec(mode, op, cur_r_s, sub_size - cur_r_s);
      }

      offset+=sub_size;
    }
    else if(full_r_s<=offset+sub_size && full_r_e>offset)
    {
      range_spect cur_r_s =
        full_r_s <= offset ? range_spect{0} : full_r_s - offset;
      range_spect cur_r_e=
        full_r_e>offset+sub_size ? sub_size : full_r_e-offset;

      get_objects_rec(mode, op, cur_r_s, cur_r_e - cur_r_s);

      offset+=sub_size;
    }
  }
}

void rw_range_sett::get_objects_typecast(
  get_modet mode,
  const typecast_exprt &tc,
  const range_spect &range_start,
  const range_spect &size)
{
  const exprt &op=tc.op();

  auto op_bits = pointer_offset_bits(op.type(), ns);

  range_spect new_size = op_bits.has_value()
                           ? range_spect::to_range_spect(*op_bits)
                           : range_spect::unknown();

  if(range_start.is_unknown())
    new_size = range_spect::unknown();
  else if(!new_size.is_unknown())
  {
    if(new_size<=range_start)
      return;

    new_size-=range_start;
    new_size=std::min(size, new_size);
  }

  get_objects_rec(mode, op, range_start, new_size);
}

void rw_range_sett::get_objects_address_of(const exprt &object)
{
  if(
    object.id() == ID_string_constant || object.id() == ID_label ||
    object.id() == ID_array || object.id() == ID_null_object ||
    object.id() == ID_symbol)
  {
    // constant, nothing to do
    return;
  }
  else if(object.id()==ID_dereference)
  {
    get_objects_rec(get_modet::READ, object);
  }
  else if(object.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(object);

    get_objects_rec(get_modet::READ, address_of_exprt(index.array()));
    get_objects_rec(get_modet::READ, index.index());
  }
  else if(object.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(object);

    get_objects_rec(get_modet::READ, address_of_exprt(member.struct_op()));
  }
  else if(object.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(object);

    get_objects_rec(get_modet::READ, if_expr.cond());
    get_objects_rec(get_modet::READ, address_of_exprt(if_expr.true_case()));
    get_objects_rec(get_modet::READ, address_of_exprt(if_expr.false_case()));
  }
  else if(object.id()==ID_byte_extract_little_endian ||
          object.id()==ID_byte_extract_big_endian)
  {
    const byte_extract_exprt &be=to_byte_extract_expr(object);

    get_objects_rec(get_modet::READ, address_of_exprt(be.op()));
  }
  else if(object.id()==ID_typecast)
  {
    const typecast_exprt &tc=to_typecast_expr(object);

    get_objects_rec(get_modet::READ, address_of_exprt(tc.op()));
  }
  else
    throw "rw_range_sett: address_of '" + object.id_string() + "' not handled";
}

void rw_range_sett::add(
  get_modet mode,
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  objectst::iterator entry=
    (mode==get_modet::LHS_W?w_range_set:r_range_set)
       .insert(
         std::pair<const irep_idt &, std::unique_ptr<range_domain_baset>>(
           identifier, nullptr))
       .first;

  if(entry->second==nullptr)
    entry->second = std::make_unique<range_domaint>();

  static_cast<range_domaint&>(*entry->second).push_back(
    {range_start, range_end});
}

void rw_range_sett::get_objects_rec(
  get_modet mode,
  const exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  if(expr.id() == ID_complex_real)
    get_objects_complex_real(
      mode, to_complex_real_expr(expr), range_start, size);
  else if(expr.id() == ID_complex_imag)
    get_objects_complex_imag(
      mode, to_complex_imag_expr(expr), range_start, size);
  else if(expr.id()==ID_typecast)
    get_objects_typecast(
      mode,
      to_typecast_expr(expr),
      range_start,
      size);
  else if(expr.id()==ID_if)
    get_objects_if(mode, to_if_expr(expr), range_start, size);
  else if(expr.id()==ID_dereference)
    get_objects_dereference(
      mode,
      to_dereference_expr(expr),
      range_start,
      size);
  else if(expr.id()==ID_byte_extract_little_endian ||
          expr.id()==ID_byte_extract_big_endian)
    get_objects_byte_extract(
      mode,
      to_byte_extract_expr(expr),
      range_start,
      size);
  else if(expr.id()==ID_shl ||
          expr.id()==ID_ashr ||
          expr.id()==ID_lshr)
    get_objects_shift(mode, to_shift_expr(expr), range_start, size);
  else if(expr.id()==ID_member)
    get_objects_member(mode, to_member_expr(expr), range_start, size);
  else if(expr.id()==ID_index)
    get_objects_index(mode, to_index_expr(expr), range_start, size);
  else if(expr.id()==ID_array)
    get_objects_array(mode, to_array_expr(expr), range_start, size);
  else if(expr.id()==ID_struct)
    get_objects_struct(mode, to_struct_expr(expr), range_start, size);
  else if(expr.id()==ID_symbol)
  {
    const symbol_exprt &symbol=to_symbol_expr(expr);
    const irep_idt identifier=symbol.get_identifier();

    auto symbol_bits = pointer_offset_bits(symbol.type(), ns);

    range_spect full_size = symbol_bits.has_value()
                              ? range_spect::to_range_spect(*symbol_bits)
                              : range_spect::unknown();

    if(
      !full_size.is_unknown() &&
      (full_size == range_spect{0} ||
       (full_size > range_spect{0} && !range_start.is_unknown() &&
        range_start >= full_size)))
    {
      // nothing to do, these are effectively constants (like function
      // symbols or structs with no members)
      // OR: invalid memory accesses
    }
    else if(!range_start.is_unknown() && range_start >= range_spect{0})
    {
      range_spect range_end =
        size.is_unknown() ? range_spect::unknown() : range_start + size;
      if(!size.is_unknown() && !full_size.is_unknown())
        range_end=std::min(range_end, full_size);

      add(mode, identifier, range_start, range_end);
    }
    else
      add(mode, identifier, range_spect{0}, range_spect::unknown());
  }
  else if(mode==get_modet::READ && expr.id()==ID_address_of)
    get_objects_address_of(to_address_of_expr(expr).object());
  else if(mode==get_modet::READ)
  {
    // possibly affects the full object size, even if range_start/size
    // are only a subset of the bytes (e.g., when using the result of
    // arithmetic operations)
    for(const auto &op : expr.operands())
      get_objects_rec(mode, op);
  }
  else if(expr.id() == ID_null_object ||
          expr.id() == ID_string_constant)
  {
    // dereferencing may yield some weird ones, ignore these
  }
  else if(mode==get_modet::LHS_W)
  {
    for(const auto &op : expr.operands())
      get_objects_rec(mode, op);
  }
  else
    throw "rw_range_sett: assignment to '" + expr.id_string() + "' not handled";
}

void rw_range_sett::get_objects_rec(get_modet mode, const exprt &expr)
{
  auto expr_bits = pointer_offset_bits(expr.type(), ns);

  range_spect size = expr_bits.has_value()
                       ? range_spect::to_range_spect(*expr_bits)
                       : range_spect::unknown();

  get_objects_rec(mode, expr, range_spect{0}, size);
}

void rw_range_sett::get_objects_rec(const typet &type)
{
  // TODO should recurse into various composite types
  if(type.id()==ID_array)
  {
    const auto &array_type = to_array_type(type);
    get_objects_rec(array_type.element_type());
    get_objects_rec(get_modet::READ, array_type.size());
  }
}

void rw_range_sett::get_array_objects(
  const irep_idt &,
  goto_programt::const_targett,
  get_modet mode,
  const exprt &pointer)
{
  object_descriptor_exprt ode;
  ode.build(dereference_exprt{skip_typecast(pointer)}, ns);
  get_objects_rec(
    mode, ode.root_object(), range_spect::unknown(), range_spect::unknown());
}

void rw_range_set_value_sett::get_objects_dereference(
  get_modet mode,
  const dereference_exprt &deref,
  const range_spect &range_start,
  const range_spect &size)
{
  rw_range_sett::get_objects_dereference(
    mode,
    deref,
    range_start,
    size);

  exprt object=deref;
  dereference(function, target, object, ns, value_sets, message_handler);

  auto type_bits = pointer_offset_bits(object.type(), ns);

  range_spect new_size = range_spect::unknown();

  if(type_bits.has_value())
  {
    new_size = range_spect::to_range_spect(*type_bits);

    if(range_start.is_unknown() || new_size <= range_start)
      new_size = range_spect::unknown();
    else
    {
      new_size -= range_start;
      new_size = std::min(size, new_size);
    }
  }

  // value_set_dereferencet::build_reference_to will turn *p into
  // DYNAMIC_OBJECT(p) ? *p : invalid_objectN
  if(object.is_not_nil() && !has_subexpr(object, ID_dereference))
    get_objects_rec(mode, object, range_start, new_size);
}

void guarded_range_domaint::output(
  const namespacet &ns, std::ostream &out) const
{
  out << "[";
  for(const_iterator itr=begin();
      itr!=end();
      ++itr)
  {
    if(itr!=begin())
      out << ";";
    out << itr->first << ":" << itr->second.first;
    // we don't know what mode (language) we are in, so we rely on the default
    // language to be reasonable for from_expr
    out << " if " << from_expr(ns, irep_idt(), itr->second.second);
  }
  out << "]";
}

void rw_guarded_range_set_value_sett::get_objects_if(
  get_modet mode,
  const if_exprt &if_expr,
  const range_spect &range_start,
  const range_spect &size)
{
  if(if_expr.cond().is_false())
    get_objects_rec(mode, if_expr.false_case(), range_start, size);
  else if(if_expr.cond().is_true())
    get_objects_rec(mode, if_expr.true_case(), range_start, size);
  else
  {
    get_objects_rec(get_modet::READ, if_expr.cond());

    guardt copy = guard;

    guard.add(not_exprt(if_expr.cond()));
    get_objects_rec(mode, if_expr.false_case(), range_start, size);
    guard = copy;

    guard.add(if_expr.cond());
    get_objects_rec(mode, if_expr.true_case(), range_start, size);
    guard = std::move(copy);
  }
}

void rw_guarded_range_set_value_sett::add(
  get_modet mode,
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  objectst::iterator entry=
    (mode==get_modet::LHS_W?w_range_set:r_range_set)
      .insert(
        std::pair<const irep_idt &, std::unique_ptr<range_domain_baset>>(
          identifier, nullptr))
      .first;

  if(entry->second==nullptr)
    entry->second = std::make_unique<guarded_range_domaint>();

  static_cast<guarded_range_domaint&>(*entry->second).insert(
    {range_start, {range_end, guard.as_expr()}});
}

static void goto_rw_assign(
  const irep_idt &function,
  goto_programt::const_targett target,
  const exprt &lhs,
  const exprt &rhs,
  rw_range_sett &rw_set)
{
  rw_set.get_objects_rec(
    function, target, rw_range_sett::get_modet::LHS_W, lhs);
  rw_set.get_objects_rec(function, target, rw_range_sett::get_modet::READ, rhs);
}

static void goto_rw_other(
  const irep_idt &function,
  goto_programt::const_targett target,
  const codet &code,
  rw_range_sett &rw_set)
{
  const irep_idt &statement = code.get_statement();

  if(statement == ID_printf)
  {
    // if it's printf, mark the operands as read here
    for(const auto &op : code.operands())
    {
      rw_set.get_objects_rec(
        function, target, rw_range_sett::get_modet::READ, op);
    }
  }
  else if(statement == ID_array_equal)
  {
    // mark the dereferenced operands as being read
    PRECONDITION(code.operands().size() == 3);
    rw_set.get_array_objects(
      function, target, rw_range_sett::get_modet::READ, code.op0());
    rw_set.get_array_objects(
      function, target, rw_range_sett::get_modet::READ, code.op1());
    // the third operand is the result
    rw_set.get_objects_rec(
      function, target, rw_range_sett::get_modet::LHS_W, code.op2());
  }
  else if(statement == ID_array_set)
  {
    PRECONDITION(code.operands().size() == 2);
    rw_set.get_array_objects(
      function, target, rw_range_sett::get_modet::LHS_W, code.op0());
    rw_set.get_objects_rec(
      function, target, rw_range_sett::get_modet::READ, code.op1());
  }
  else if(statement == ID_array_copy || statement == ID_array_replace)
  {
    PRECONDITION(code.operands().size() == 2);
    rw_set.get_array_objects(
      function, target, rw_range_sett::get_modet::LHS_W, code.op0());
    rw_set.get_array_objects(
      function, target, rw_range_sett::get_modet::READ, code.op1());
  }
  else if(statement == ID_havoc_object)
  {
    PRECONDITION(code.operands().size() == 1);
    // re-use get_array_objects as this havoc_object affects whatever is the
    // object being the pointer that code.op0() is
    rw_set.get_array_objects(
      function, target, rw_range_sett::get_modet::LHS_W, code.op0());
  }
}

static void goto_rw(
  const irep_idt &function,
  goto_programt::const_targett target,
  const exprt &lhs,
  const exprt &function_expr,
  const exprt::operandst &arguments,
  rw_range_sett &rw_set)
{
  if(lhs.is_not_nil())
    rw_set.get_objects_rec(
      function, target, rw_range_sett::get_modet::LHS_W, lhs);

  rw_set.get_objects_rec(
    function, target, rw_range_sett::get_modet::READ, function_expr);

  for(const auto &argument : arguments)
  {
    rw_set.get_objects_rec(
      function, target, rw_range_sett::get_modet::READ, argument);
  }
}

void goto_rw(
  const irep_idt &function,
  goto_programt::const_targett target,
  rw_range_sett &rw_set)
{
  switch(target->type())
  {
  case NO_INSTRUCTION_TYPE:
  case INCOMPLETE_GOTO:
    UNREACHABLE;
    break;

  case GOTO:
  case ASSUME:
  case ASSERT:
    rw_set.get_objects_rec(
      function, target, rw_range_sett::get_modet::READ, target->condition());
    break;

  case SET_RETURN_VALUE:
    rw_set.get_objects_rec(
      function, target, rw_range_sett::get_modet::READ, target->return_value());
    break;

  case OTHER:
    goto_rw_other(function, target, target->get_other(), rw_set);
    break;

  case SKIP:
  case START_THREAD:
  case END_THREAD:
  case LOCATION:
  case END_FUNCTION:
  case ATOMIC_BEGIN:
  case ATOMIC_END:
  case THROW:
  case CATCH:
    // these don't read or write anything
    break;

  case ASSIGN:
    goto_rw_assign(
      function, target, target->assign_lhs(), target->assign_rhs(), rw_set);
    break;

  case DEAD:
    rw_set.get_objects_rec(
      function, target, rw_range_sett::get_modet::LHS_W, target->dead_symbol());
    break;

  case DECL:
    rw_set.get_objects_rec(function, target, target->decl_symbol().type());
    rw_set.get_objects_rec(
      function, target, rw_range_sett::get_modet::LHS_W, target->decl_symbol());
    break;

  case FUNCTION_CALL:
    goto_rw(
      function,
      target,
      target->call_lhs(),
      target->call_function(),
      target->call_arguments(),
      rw_set);
    break;
  }
}

void goto_rw(
  const irep_idt &function,
  const goto_programt &goto_program,
  rw_range_sett &rw_set)
{
  forall_goto_program_instructions(i_it, goto_program)
    goto_rw(function, i_it, rw_set);
}

void goto_rw(const goto_functionst &goto_functions,
             const irep_idt &function,
             rw_range_sett &rw_set)
{
  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(function);

  if(f_it!=goto_functions.function_map.end())
  {
    const goto_programt &body=f_it->second.body;

    goto_rw(f_it->first, body, rw_set);
  }
}
