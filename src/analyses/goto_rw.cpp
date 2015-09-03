/*******************************************************************\

Module: 

Author: Daniel Kroening

Date: April 2010

\*******************************************************************/

#include <limits>
#include <algorithm>

#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/pointer_offset_size.h>
#include <util/byte_operators.h>
#include <util/endianness_map.h>
#include <util/arith_tools.h>
#include <util/simplify_expr.h>

#include <goto-programs/goto_functions.h>

#include <pointer-analysis/goto_program_dereference.h>

#include "goto_rw.h"

/*******************************************************************\

Function: range_domain_baset::~range_domain_baset

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

range_domain_baset::~range_domain_baset()
{
}

/*******************************************************************\

Function: range_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void range_domaint::output(
  const namespacet &ns, std::ostream &out) const
{
  out << "[";
  for(const_iterator itr=begin();
      itr!=end();
      ++itr)
  {
    if(itr!=begin()) out << ";";
    out << itr->first << ":" << itr->second;
  }
  out << "]";
}

/*******************************************************************\

Function: rw_range_sett::~rw_range_sett

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

rw_range_sett::~rw_range_sett()
{
  for(rw_range_sett::objectst::iterator it=r_range_set.begin();
      it!=r_range_set.end();
      ++it)
    delete it->second;

  for(rw_range_sett::objectst::iterator it=w_range_set.begin();
      it!=w_range_set.end();
      ++it)
    delete it->second;
}

/*******************************************************************\

Function: rw_range_sett::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::output(std::ostream &out) const
{
  out << "READ:" << std::endl;
  forall_rw_range_set_r_objects(it, *this)
  {
    out << "  " << it->first;
    it->second->output(ns, out);
    out << std::endl;
  }

  out << std::endl;

  out << "WRITE:" << std::endl;
  forall_rw_range_set_w_objects(it, *this)
  {
    out << "  " << it->first;
    it->second->output(ns, out);
    out << std::endl;
  }
}

/*******************************************************************\

Function: rw_range_sett::get_objects_complex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_complex(
  get_modet mode,
  const exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  const exprt &op=expr.op0();
  assert(op.type().id()==ID_complex);

  range_spect sub_size=
    to_range_spect(pointer_offset_bits(op.type().subtype(), ns));
  range_spect offset=
    (range_start==-1 || expr.id()==ID_complex_real) ? 0 : sub_size;

  get_objects_rec(mode, op, range_start+offset, size);
}

/*******************************************************************\

Function: rw_range_sett::get_objects_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    get_objects_rec(READ, if_expr.cond());

    get_objects_rec(mode, if_expr.false_case(), range_start, size);
    get_objects_rec(mode, if_expr.true_case(), range_start, size);
  }
}

/*******************************************************************\

Function: rw_range_sett::get_objects_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_dereference(
  get_modet mode,
  const dereference_exprt &deref,
  const range_spect &range_start,
  const range_spect &size)
{
  const exprt &pointer=deref.pointer();
  get_objects_rec(READ, pointer);
}

/*******************************************************************\

Function: rw_range_sett::get_objects_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_byte_extract(
  get_modet mode,
  const byte_extract_exprt &be,
  const range_spect &range_start,
  const range_spect &size)
{
  const exprt simp_offset=simplify_expr(be.offset(), ns);

  mp_integer index;
  if(range_start==-1 || to_integer(simp_offset, index))
    get_objects_rec(mode, be.op(), -1, size);
  else
  {
    index*=8;
    if(index>=pointer_offset_bits(be.op().type(), ns))
      return;

    endianness_mapt map(
      be.op().type(),
      be.id()==ID_byte_extract_little_endian,
      ns);
    assert(index<std::numeric_limits<size_t>::max());
    range_spect offset=range_start + map.map_bit(integer2long(index));
    get_objects_rec(mode, be.op(), offset, size);
  }
}

/*******************************************************************\

Function: rw_range_sett::get_objects_shift

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_shift(
  get_modet mode,
  const shift_exprt &shift,
  const range_spect &range_start,
  const range_spect &size)
{
  const exprt simp_distance=simplify_expr(shift.distance(), ns);

  range_spect src_size=
    to_range_spect(pointer_offset_bits(shift.op().type(), ns));

  mp_integer dist;
  if(range_start==-1 ||
     size==-1 ||
     src_size==-1 ||
     to_integer(simp_distance, dist))
  {
    get_objects_rec(mode, shift.op(), -1, -1);
    get_objects_rec(mode, shift.distance(), -1, -1);
  }
  else
  {
    range_spect dist_r=to_range_spect(dist);

    // not sure whether to worry about
    // config.ansi_c.endianness==configt::ansi_ct::IS_LITTLE_ENDIAN
    // right here maybe?

    if(shift.id()==ID_ashr || shift.id()==ID_lshr)
    {
      range_spect sh_range_start=range_start;
      sh_range_start+=dist_r;

      range_spect sh_size=std::min(size, src_size-sh_range_start);

      if(sh_range_start>=0 && sh_range_start<src_size)
        get_objects_rec(mode, shift.op(), sh_range_start, sh_size);
    }
    else
    {
      assert(src_size-dist_r>=0);
      range_spect sh_size=std::min(size, src_size-dist_r);

      get_objects_rec(mode, shift.op(), range_start, sh_size);
    }
  }
}

/*******************************************************************\

Function: rw_range_sett::get_objects_member

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_member(
  get_modet mode,
  const member_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  const typet &type=ns.follow(expr.struct_op().type());

  if(type.id()==ID_union ||
     range_start==-1)
  {
    get_objects_rec(mode, expr.struct_op(), range_start, size);
    return;
  }

  const struct_typet &struct_type=to_struct_type(type);

  // TODO - assumes members are byte-aligned
  range_spect offset=
    to_range_spect(member_offset(
        struct_type,
        expr.get_component_name(),
        ns) * 8);

  if(offset!=-1)
    offset+=range_start;

  get_objects_rec(mode, expr.struct_op(), offset, size);
}

/*******************************************************************\

Function: rw_range_sett::get_objects_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_index(
  get_modet mode,
  const index_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  if(expr.array().id()=="NULL-object")
    return;

  range_spect sub_size=0;
  const typet &type=ns.follow(expr.array().type());

  if(type.id()==ID_vector)
  {
    const vector_typet &vector_type=to_vector_type(type);

    sub_size=
      to_range_spect(pointer_offset_bits(vector_type.subtype(), ns));
  }
  else
  {
    const array_typet &array_type=to_array_type(type);

    sub_size=
      to_range_spect(pointer_offset_bits(array_type.subtype(), ns));
  }

  const exprt simp_index=simplify_expr(expr.index(), ns);

  mp_integer index;
  if(to_integer(simp_index, index))
  {
    get_objects_rec(READ, expr.index());
    index=-1;
  }

  if(range_start==-1 ||
     sub_size==-1 ||
     index==-1)
    get_objects_rec(mode, expr.array(), -1, size);
  else
    get_objects_rec(
      mode,
      expr.array(),
      range_start+to_range_spect(index*sub_size),
      size);
}

/*******************************************************************\

Function: rw_range_sett::get_objects_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_array(
  get_modet mode,
  const array_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  const array_typet &array_type=
    to_array_type(ns.follow(expr.type()));

  range_spect sub_size=
    to_range_spect(pointer_offset_bits(array_type.subtype(), ns));

  if(sub_size==-1)
  {
    forall_operands(it, expr)
      get_objects_rec(mode, *it, 0, -1);

    return;
  }

  range_spect offset=0;
  range_spect full_r_s=range_start==-1 ? 0 : range_start;
  range_spect full_r_e=
    size==-1 ? sub_size*expr.operands().size() : full_r_s+size;

  forall_operands(it, expr)
  {
    if(full_r_s<=offset+sub_size && full_r_e>offset)
    {
      range_spect cur_r_s=full_r_s<=offset ? 0 : full_r_s-offset;
      range_spect cur_r_e=
        full_r_e>offset+sub_size ? sub_size : full_r_e-offset;

      get_objects_rec(mode, *it, cur_r_s, cur_r_e-cur_r_s);
    }

    offset+=sub_size;
  }
}

/*******************************************************************\

Function: rw_range_sett::get_objects_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_struct(
  get_modet mode,
  const struct_exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  const struct_typet &struct_type=
    to_struct_type(ns.follow(expr.type()));

  range_spect full_size=
    to_range_spect(pointer_offset_bits(struct_type, ns));

  range_spect offset=0;
  range_spect full_r_s=range_start==-1 ? 0 : range_start;
  range_spect full_r_e=size==-1 || full_size==-1 ? -1 : full_r_s+size;

  forall_operands(it, expr)
  {
    range_spect sub_size=
      to_range_spect(pointer_offset_bits(it->type(), ns));

    if(offset==-1)
    {
      get_objects_rec(mode, *it, 0, sub_size);
    }
    else if(sub_size==-1)
    {
      if(full_r_e==-1 || full_r_e>offset)
      {
        range_spect cur_r_s=full_r_s<=offset ? 0 : full_r_s-offset;

        get_objects_rec(mode, *it, cur_r_s, -1);
      }

      offset=-1;
    }
    else if(full_r_e==-1)
    {
      if(full_r_s<=offset+sub_size)
      {
        range_spect cur_r_s=full_r_s<=offset ? 0 : full_r_s-offset;

        get_objects_rec(mode, *it, cur_r_s, sub_size-cur_r_s);
      }

      offset+=sub_size;
    }
    else if(full_r_s<=offset+sub_size && full_r_e>offset)
    {
      range_spect cur_r_s=full_r_s<=offset ? 0 : full_r_s-offset;
      range_spect cur_r_e=
        full_r_e>offset+sub_size ? sub_size : full_r_e-offset;

      get_objects_rec(mode, *it, cur_r_s, cur_r_e-cur_r_s);

      offset+=sub_size;
    }
  }
}

/*******************************************************************\

Function: rw_range_sett::get_objects_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_typecast(
  get_modet mode,
  const typecast_exprt &tc,
  const range_spect &range_start,
  const range_spect &size)
{
  const exprt& op=tc.op();

  range_spect new_size=
    to_range_spect(pointer_offset_bits(op.type(), ns));

  if(range_start==-1)
    new_size=-1;
  else if(new_size!=-1)
  {
    if(new_size<=range_start)
      return;

    new_size-=range_start;
    new_size=std::min(size, new_size);
  }

  get_objects_rec(mode, op, range_start, new_size);
}

/*******************************************************************\

Function: rw_range_sett::get_objects_address_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_address_of(const exprt &object)
{
  if(object.id()==ID_symbol ||
     object.id()==ID_string_constant ||
     object.id()==ID_label ||
     object.id()==ID_array ||
     object.id()=="NULL-object")
    // constant, nothing to do
    return;
  else if(object.id()==ID_dereference)
    get_objects_rec(READ, object);
  else if(object.id()==ID_index)
  {
    const index_exprt &index=to_index_expr(object);

    get_objects_rec(READ, address_of_exprt(index.array()));
    get_objects_rec(READ, index.index());
  }
  else if(object.id()==ID_member)
  {
    const member_exprt &member=to_member_expr(object);

    get_objects_rec(READ, address_of_exprt(member.struct_op()));
  }
  else if(object.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(object);

    get_objects_rec(READ, if_expr.cond());
    get_objects_rec(READ, address_of_exprt(if_expr.true_case()));
    get_objects_rec(READ, address_of_exprt(if_expr.false_case()));
  }
  else if(object.id()==ID_byte_extract_little_endian ||
          object.id()==ID_byte_extract_big_endian)
  {
    const byte_extract_exprt &be=to_byte_extract_expr(object);

    get_objects_rec(READ, address_of_exprt(be.op()));
  }
  else if(object.id()==ID_typecast)
  {
    const typecast_exprt &tc=to_typecast_expr(object);

    get_objects_rec(READ, address_of_exprt(tc.op()));
  }
  else
    throw "rw_range_sett: address_of `"+object.id_string()+"' not handled";
}

/*******************************************************************\

Function: rw_range_sett::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::add(
  get_modet mode,
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  objectst::iterator entry=(mode==LHS_W ? w_range_set : r_range_set).
    insert(std::make_pair<const irep_idt&, range_domain_baset*>(identifier, 0)).first;

  if(entry->second==0)
    entry->second=new range_domaint();

  static_cast<range_domaint*>(entry->second)->push_back(
    std::make_pair(range_start, range_end));
}

/*******************************************************************\

Function: rw_range_sett::get_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_rec(
  get_modet mode,
  const exprt &expr,
  const range_spect &range_start,
  const range_spect &size)
{
  if(expr.id()==ID_complex_real ||
     expr.id()==ID_complex_imag)
    get_objects_complex(mode, expr, range_start, size);
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
    range_spect full_size=
      to_range_spect(pointer_offset_bits(symbol.type(), ns));

    if(full_size==0 ||
       (full_size>0 && range_start>=full_size))
    {
      // nothing to do, these are effectively constants (like function
      // symbols or structs with no members)
      // OR: invalid memory accesses
    }
    else if(range_start>=0)
    {
      range_spect range_end=size==-1 ? -1 : range_start+size;
      if(size!=-1 && full_size!=-1)
        range_end=std::max(range_end, full_size);

      add(mode, identifier, range_start, range_end);
    }
    else
      add(mode, identifier, 0, -1);
  }
  else if(mode==READ && expr.id()==ID_address_of)
    get_objects_address_of(to_address_of_expr(expr).object());
  else if(mode==READ)
  {
    // possibly affects the full object size, even if range_start/size
    // are only a subset of the bytes (e.g., when using the result of
    // arithmetic operations)
    forall_operands(it, expr)
      get_objects_rec(mode, *it);
  }
  else if(expr.id()=="NULL-object" ||
          expr.id()==ID_string_constant)
  {
    // dereferencing may yield some weird ones, ignore these
  }
  else
    throw "rw_range_sett: assignment to `"+expr.id_string()+"' not handled";
}

/*******************************************************************\

Function: rw_range_sett::get_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_rec(get_modet mode, const exprt &expr)
{
  range_spect size=
    to_range_spect(pointer_offset_bits(expr.type(), ns));
  get_objects_rec(mode, expr, 0, size);
}

/*******************************************************************\

Function: rw_range_sett::get_objects_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_range_sett::get_objects_rec(const typet &type)
{
  // TODO should recurse into various composite types
  if(type.id()==ID_array)
  {
    get_objects_rec(type.subtype());
    get_objects_rec(READ, to_array_type(type).size());
  }
}

/*******************************************************************\

Function: rw_range_set_value_sett::get_objects_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  dereference(target, object, ns, value_sets);

  range_spect new_size=
    to_range_spect(pointer_offset_bits(object.type(), ns));

  if(range_start==-1 || new_size<=range_start)
    new_size=-1;
  else
  {
    new_size-=range_start;
    new_size=std::min(size, new_size);
  }

  if(object.is_not_nil() && object!=deref)
    get_objects_rec(mode, object, range_start, new_size);
}

/*******************************************************************\

Function: guarded_range_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void guarded_range_domaint::output(
  const namespacet &ns, std::ostream &out) const
{
  out << "[";
  for(const_iterator itr=begin();
      itr!=end();
      ++itr)
  {
    if(itr!=begin()) out << ";";
    out << itr->first << ":" << itr->second.first;
    out << " if " << from_expr(ns, "", itr->second.second);
  }
  out << "]";
}

/*******************************************************************\

Function: rw_guarded_range_set_value_sett::get_objects_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    get_objects_rec(READ, if_expr.cond());

    guardt guard_bak1(guard), guard_bak2(guard);

    guard.add(not_exprt(if_expr.cond()));
    get_objects_rec(mode, if_expr.false_case(), range_start, size);
    guard.swap(guard_bak1);

    guard.add(if_expr.cond());
    get_objects_rec(mode, if_expr.true_case(), range_start, size);
    guard.swap(guard_bak2);
  }
}

/*******************************************************************\

Function: rw_guarded_range_set_value_sett::add

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rw_guarded_range_set_value_sett::add(
  get_modet mode,
  const irep_idt &identifier,
  const range_spect &range_start,
  const range_spect &range_end)
{
  objectst::iterator entry=(mode==LHS_W ? w_range_set : r_range_set).
    insert(std::make_pair<const irep_idt&, range_domain_baset*>(identifier, 0)).first;

  if(entry->second==0)
    entry->second=new guarded_range_domaint();

  static_cast<guarded_range_domaint*>(entry->second)->insert(
    std::make_pair(range_start,
                   std::make_pair(range_end, guard.as_expr())));
}

/*******************************************************************\

Function: goto_rw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_rw(goto_programt::const_targett target,
             const code_assignt &assign,
             rw_range_sett &rw_set)
{
  rw_set.get_objects_rec(target, rw_range_sett::LHS_W, assign.lhs());
  rw_set.get_objects_rec(target, rw_range_sett::READ, assign.rhs());
}

/*******************************************************************\

Function: goto_rw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_rw(goto_programt::const_targett target,
             const code_function_callt &function_call,
             rw_range_sett &rw_set)
{
  if(function_call.lhs().is_not_nil())
    rw_set.get_objects_rec(
      target,
      rw_range_sett::LHS_W,
      function_call.lhs());

  rw_set.get_objects_rec(
    target,
    rw_range_sett::READ,
    function_call.function());

  forall_expr(it, function_call.arguments())
    rw_set.get_objects_rec(target, rw_range_sett::READ, *it);
}

/*******************************************************************\

Function: goto_rw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_rw(goto_programt::const_targett target,
             rw_range_sett &rw_set)
{
  switch(target->type)
  {
  case NO_INSTRUCTION_TYPE:
    assert(false);
    break;
    
  case GOTO:
  case ASSUME:
  case ASSERT:
    rw_set.get_objects_rec(
      target,
      rw_range_sett::READ,
      target->guard);
    break;
    
  case RETURN:
    {
      const code_returnt &code_return=
        to_code_return(target->code);
      if(code_return.has_return_value())
        rw_set.get_objects_rec(
          target,
          rw_range_sett::READ,
          code_return.return_value());
    }
    break;
    
  case OTHER:
    // don't know
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
    goto_rw(target, to_code_assign(target->code), rw_set);
    break;
  
  case DEAD:
    rw_set.get_objects_rec(
      target,
      rw_range_sett::LHS_W,
      to_code_dead(target->code).symbol());
    break;

  case DECL:
    rw_set.get_objects_rec(
      to_code_decl(target->code).symbol().type());
    rw_set.get_objects_rec(
      target,
      rw_range_sett::LHS_W,
      to_code_decl(target->code).symbol());
    break;
  
  case FUNCTION_CALL:
    goto_rw(target, to_code_function_call(target->code), rw_set);
    break;
  }
}

/*******************************************************************\

Function: goto_rw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_rw(const goto_programt &goto_program, rw_range_sett &rw_set)
{
  forall_goto_program_instructions(i_it, goto_program)
    goto_rw(i_it, rw_set);
}

/*******************************************************************\

Function: goto_rw

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_rw(const goto_functionst &goto_functions,
             const irep_idt &function,
             rw_range_sett &rw_set)
{
  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(function);

  if(f_it!=goto_functions.function_map.end())
  {
    const goto_programt &body=f_it->second.body;

    goto_rw(body, rw_set);
  }
}

