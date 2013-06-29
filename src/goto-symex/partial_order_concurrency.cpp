/*******************************************************************\

Module: Add constraints to equation encoding partial orders on events

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <limits>

#include <util/i2string.h>
#include <util/arith_tools.h>

#include "partial_order_concurrency.h"

/*******************************************************************\

Function: partial_order_concurrencyt::~partial_order_concurrencyt

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

partial_order_concurrencyt::partial_order_concurrencyt(
  const namespacet &_ns):ns(_ns)
{
}

/*******************************************************************\

Function: partial_order_concurrencyt::~partial_order_concurrencyt

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

partial_order_concurrencyt::~partial_order_concurrencyt()
{
}

/*******************************************************************\

Function: partial_order_concurrencyt::build_event_lists

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::build_event_lists(
  symex_target_equationt &equation)
{
  // a per-thread counter
  std::map<unsigned, unsigned> counter;

  for(eventst::const_iterator
      e_it=equation.SSA_steps.begin();
      e_it!=equation.SSA_steps.end();
      e_it++)
  {
    if(is_shared_read(e_it) ||
       is_shared_write(e_it) ||
       is_spawn(e_it))
    {
      unsigned thread_nr=e_it->source.thread_nr;

      if(!is_spawn(e_it))
      {
        a_rect &a_rec=address_map[address(e_it)];

        if(is_shared_read(e_it))
          a_rec.reads.push_back(e_it);
        else // must be write
          a_rec.writes.push_back(e_it);
      }

      // maps an event id to a per-thread counter
      unsigned cnt=counter[thread_nr]++;
      numbering[e_it]=cnt;
    }
  }
}

/*******************************************************************\

Function: partial_order_concurrencyt::rw_clock_id

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt partial_order_concurrencyt::rw_clock_id(event_it event)
{
  if(event->is_shared_write())
    return id2string(id(event))+"$wclk";
  else if(event->is_shared_read())
    return id2string(id(event))+"$rclk";
  else
    assert(false);

  return "";
}

/*******************************************************************\

Function: partial_order_concurrencyt::clock

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt partial_order_concurrencyt::clock(event_it event)
{
  irep_idt identifier;
  assert(!numbering.empty());

  if(event->is_shared_write())
  {
    assert(is_shared_write(event));
    identifier=rw_clock_id(event);
  }
  else if(event->is_shared_read())
  {
    assert(is_shared_read(event));
    identifier=rw_clock_id(event);
  }
  else if(event->is_spawn())
  {
    assert(is_spawn(event));
    identifier=
      i2string(event->source.thread_nr+1)+"$"+
      i2string(numbering[event])+"$spwnclk";
  }
  else
    assert(false);

  return symbol_exprt(identifier, clock_type);
}

/*******************************************************************\

Function: partial_order_concurrencyt::is_shared_write

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

bool partial_order_concurrencyt::is_shared_write(event_it event) const
{
  if(!event->is_shared_write()) return false;
  const irep_idt identifier=event->original_lhs_object.get_identifier();
  if(identifier=="goto_symex::\\guard") return false;
  const symbolt &symbol=ns.lookup(identifier);
  return !symbol.is_thread_local;
}

/*******************************************************************\

Function: partial_order_concurrencyt::is_shared_read

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

bool partial_order_concurrencyt::is_shared_read(event_it event) const
{
  if(!event->is_shared_read()) return false;
  const irep_idt identifier=event->original_lhs_object.get_identifier();
  if(identifier=="goto_symex::\\guard") return false;
  const symbolt &symbol=ns.lookup(identifier);
  return !symbol.is_thread_local;
}

/*******************************************************************\

Function: partial_order_concurrencyt::build_clock_type

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::build_clock_type(
  const symex_target_equationt &equation)
{
  mp_integer width=address_bits(equation.SSA_steps.size());
  assert(width<std::numeric_limits<unsigned>::max());
  clock_type=unsignedbv_typet(integer2long(width));
}

/*******************************************************************\

Function: partial_order_concurrencyt::before

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

exprt partial_order_concurrencyt::before(
  event_it e1, event_it e2)
{
  #if 0
  if(e1->atomic_section_id!=0 &&
     e1->atomic_section_id==e2->atomic_section_id)
    return equal_exprt(clock(e1), clock(e2));
  else
  #endif
    return binary_relation_exprt(clock(e1), ID_lt, clock(e2));
}

