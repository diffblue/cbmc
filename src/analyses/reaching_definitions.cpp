/*******************************************************************\

Module: Range-based reaching definitions analysis (following Field-
        Sensitive Program Dependence Analysis, Litvak et al., FSE 2010)

Author: Michael Tautschnig

Date: February 2013

\*******************************************************************/

#include <limits>
#include <algorithm>

#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/pointer_offset_size.h>
#include <util/byte_operators.h>
#include <util/arith_tools.h>

#include "reaching_definitions.h"

/*******************************************************************\

Function: rd_range_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::transform(
  const namespacet &ns,
  locationt from,
  locationt to)
{
  if(from->is_dead())
  {
    const symbol_exprt &symbol=
      to_symbol_expr(to_code_dead(from->code).symbol());
    values.erase(symbol.get_identifier());
    return;
  }
  else if(!from->is_assign())
    return;

  const exprt &lhs=to_code_assign(from->code).lhs();

  if(lhs.id()==ID_complex_real ||
          lhs.id()==ID_complex_imag)
  {
    assert(lhs.type().id()==ID_complex);
    mp_integer offset=compute_pointer_offset(lhs.op0(), ns);
    mp_integer sub_size=pointer_offset_size(lhs.type().subtype(), ns);

    assign(
      ns,
      from,
      lhs.op0(),
      offset+((offset==-1 || lhs.id()==ID_complex_real) ? 0 : sub_size),
      sub_size);
  }
  else
  {
    mp_integer size=pointer_offset_size(lhs.type(), ns);

    assign(ns, from, lhs, size);
  }
}

/*******************************************************************\

Function: rd_range_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::assign(
  const namespacet &ns,
  locationt from,
  const exprt &lhs,
  const mp_integer &size)
{
  if(lhs.id()==ID_typecast)
    assign(ns, from, to_typecast_expr(lhs).op(), size);
  else if(lhs.id()==ID_if)
    assign_if(ns, from, to_if_expr(lhs), size);
  else if(lhs.id()==ID_dereference)
    assign_dereference(ns, from, to_dereference_expr(lhs), size);
  else if(lhs.id()==ID_byte_extract_little_endian ||
          lhs.id()==ID_byte_extract_big_endian)
    assign_byte_extract(ns, from, to_byte_extract_expr(lhs), size);
  else if(lhs.id()==ID_symbol ||
          lhs.id()==ID_index ||
          lhs.id()==ID_member)
    assign(ns, from, lhs, compute_pointer_offset(lhs, ns), size);
  else
    throw "assignment to `"+lhs.id_string()+"' not handled";
}

/*******************************************************************\

Function: rd_range_domaint::assign_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::assign_if(
  const namespacet &ns,
  locationt from,
  const if_exprt &if_expr,
  const mp_integer &size)
{
  if(if_expr.cond().is_false())
    assign(ns, from, if_expr.false_case(), size);
  else if(if_expr.cond().is_true())
    assign(ns, from, if_expr.true_case(), size);
  else
  {
    rd_range_domaint false_case(*this);
    assign(ns, from, if_expr.false_case(), size);
    values.swap(false_case.values);
    assign(ns, from, if_expr.true_case(), size);

    merge(false_case, from);
  }
}

/*******************************************************************\

Function: rd_range_domaint::assign_dereference

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::assign_dereference(
  const namespacet &ns,
  locationt from,
  const dereference_exprt &deref,
  const mp_integer &size)
{
  assert(local_may_alias);

  const exprt &pointer=deref.pointer();
  std::set<exprt> alias_set=local_may_alias->get(from, pointer);

  valuest before(values);
  for(std::set<exprt>::const_iterator it=alias_set.begin();
      it!=alias_set.end();
      it++)
  {
    if(it->id()!=ID_unknown &&
       it->id()!=ID_dynamic_object &&
       it->id()!=ID_null_object)
    {
      valuest bak;
      bak.swap(values);

      values=before;
      assign(ns, from, *it, size);

      rd_range_domaint this_object;
      this_object.values.swap(values);
      values.swap(bak);

      merge(this_object, from);
    }
  }
}

/*******************************************************************\

Function: rd_range_domaint::assign_byte_extract

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::assign_byte_extract(
  const namespacet &ns,
  locationt from,
  const byte_extract_exprt &be,
  const mp_integer &size)
{
  assert(size==1);
  mp_integer op_offset=compute_pointer_offset(be.op(), ns);

  mp_integer index;
  if(op_offset==-1 || to_integer(be.offset(), index))
    assign(ns, from, be.op(), -1, 1);
  else
  {
    #if 0
    endianness_mapt map(
      be.op().type(),
      be.id()==ID_byte_extract_little_endian,
      ns);
    assert(index<std::numeric_limits<unsigned>::max());
    op_offset+=map.map_byte(integer2long(index));
    #else
    op_offset+=index;
    #endif
    assign(ns, from, be.op(), op_offset, 1);
  }
}

/*******************************************************************\

Function: rd_range_domaint::assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::assign(
  const namespacet &ns,
  locationt from,
  const exprt &lhs,
  const mp_integer &range_start,
  const mp_integer &size)
{
  if(lhs.id()==ID_member)
    assign(ns, from, to_member_expr(lhs).struct_op(), range_start, size);
  else if(lhs.id()==ID_index)
    assign(ns, from, to_index_expr(lhs).array(), range_start, size);
  else
  {
    const symbol_exprt &symbol=to_symbol_expr(lhs);
    const irep_idt identifier=symbol.get_identifier();

    if(range_start>=0)
    {
      kill(from, identifier, range_start, size);
      gen(from, identifier, range_start, size);
    }
    else
    {
      mp_integer full_size=pointer_offset_size(symbol.type(), ns);
      gen(from, identifier, 0, full_size);
    }
  }
}

/*******************************************************************\

Function: rd_range_domaint::kill

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::kill(
  locationt from,
  const irep_idt &identifier,
  const mp_integer &range_start,
  const mp_integer &size)
{
  assert(range_start>=0);
  // -1 for objects of infinite/unknown size
  if(size==-1)
  {
    kill_inf(from, identifier, range_start);
    return;
  }

  assert(size>0);
  mp_integer range_end=range_start+size;

  valuest::iterator entry=values.find(identifier);
  if(entry==values.end())
    return;

  rangest &ranges=entry->second;

  for(rangest::iterator it=ranges.begin();
      it!=ranges.end();
     ) // no ++it
    if(it->first >= range_end)
      break;
    else if(it->second.first!=-1 &&
            it->second.first <= range_start)
      ++it;
    else if(it->first >= range_start &&
            it->second.first!=-1 &&
            it->second.first <= range_end) // rs <= a < b <= re
    {
      ranges.erase(it++);
    }
    else if(it->first >= range_start) // rs <= a <= re < b
    {
      ranges.insert(std::make_pair(range_end, it->second));
      ranges.erase(it++);
    }
    else if(it->second.first==-1 ||
            it->second.first >= range_end) // a <= rs < re <= b
    {
      ranges.insert(std::make_pair(range_end, it->second));
      it->second.first=range_start;
      ++it;
    }
    else // a <= rs < b < re
    {
      it->second.first=range_start;
      ++it;
    }
}

/*******************************************************************\

Function: rd_range_domaint::kill_inf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::kill_inf(
  locationt from,
  const irep_idt &identifier,
  const mp_integer &range_start)
{
  assert(range_start>=0);

  valuest::iterator entry=values.find(identifier);
  if(entry==values.end())
    return;

  rangest &ranges=entry->second;

  for(rangest::iterator it=ranges.begin();
      it!=ranges.end();
     ) // no ++it
    if(it->second.first!=-1 &&
       it->second.first <= range_start)
      ++it;
    else if(it->first >= range_start) // rs <= a < b <= re
    {
      ranges.erase(it++);
    }
    else // a <= rs < b < re
    {
      it->second.first=range_start;
      ++it;
    }
}

/*******************************************************************\

Function: rd_range_domaint::gen

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool rd_range_domaint::gen(
  locationt from,
  const irep_idt &identifier,
  const mp_integer &range_start,
  const mp_integer &size)
{
  assert(range_start>=0);
  // -1 for objects of infinite/unknown size
  assert(size>0 || size==-1);
  mp_integer range_end=size==-1 ? -1 : range_start+size;

  std::pair<valuest::iterator, bool> entry=
    values.insert(std::make_pair(identifier, rangest()));
  rangest &ranges=entry.first->second;

  if(!entry.second)
    for(rangest::iterator it=ranges.begin();
        it!=ranges.end();
        ) // no ++it
    {
      if(it->second.second!=from ||
         (it->second.first!=-1 && it->second.first <= range_start) ||
         (range_end!=-1 && it->first >= range_end))
        ++it;
      else if(it->first > range_start) // rs < a < b,re
      {
        if(range_end!=-1)
          range_end=std::max(range_end, it->second.first);
        ranges.erase(it++);
      }
      else if(it->second.first==-1 ||
              (range_end!=-1 &&
               it->second.first >= range_end)) // a <= rs < re <= b
      {
        // nothing to do
        return false;
      }
      else // a <= rs < b < re
      {
        it->second.first=range_end;
        return true;
      }
    }

  ranges.insert(std::make_pair(
      range_start,
      std::make_pair(range_end, from)));

  return true;
}

/*******************************************************************\

Function: rd_range_domaint::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void rd_range_domaint::output(
  const namespacet &ns,
  std::ostream &out) const
{
  out << "Reaching definitions:" << std::endl;
  for(valuest::const_iterator
      it=values.begin();
      it!=values.end();
      ++it)
  {
    out << "  " << it->first << "[";
    for(rangest::const_iterator itr=it->second.begin();
        itr!=it->second.end();
        ++itr)
    {
      if(itr!=it->second.begin()) out << ";";
      out << itr->first << ":" << itr->second.first;
    }
    out << "]" << std::endl;
  }
}

/*******************************************************************\

Function: rd_range_domaint::merge

  Inputs:

 Outputs: returns true iff there is s.th. new

 Purpose:

\*******************************************************************/

bool rd_range_domaint::merge(
  const rd_range_domaint &other,
  locationt to)
{
  bool more=false;

  valuest::iterator it=values.begin();
  for(valuest::const_iterator ito=other.values.begin();
      ito!=other.values.end();
      ++ito)
  {
    while(it!=values.end() && it->first<ito->first)
      ++it;
    if(it==values.end() || ito->first<it->first)
    {
      values.insert(*ito);
      more=true;
    }
    else if(it!=values.end())
    {
      assert(it->first==ito->first);
      const rangest &rangeso=ito->second;
      for(rangest::const_iterator itro=rangeso.begin();
          itro!=rangeso.end();
          ++itro)
        more|=gen(
          itro->second.second,
          ito->first,
          itro->first,
          itro->second.first);
      ++it;
    }
  }

  return more;
}

/*******************************************************************\

Function: reaching_definitions_analysist::initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reaching_definitions_analysist::initialize(
  const goto_functionst &goto_functions)
{
  forall_goto_functions(f_it, goto_functions)
  {
    local_may_aliases.insert(
      std::make_pair(f_it->first, local_may_aliast(f_it->second)));
  }

  static_analysist<rd_range_domaint>::initialize(goto_functions);
}

/*******************************************************************\

Function: reaching_definitions_analysist::generate_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void reaching_definitions_analysist::generate_state(locationt l)
{
  static_analysist<rd_range_domaint>::generate_state(l);

  may_aliasest::iterator entry=
    local_may_aliases.find(l->function);
  if(entry!=local_may_aliases.end())
    state_map[l].set_may_alias(&(entry->second));
}

