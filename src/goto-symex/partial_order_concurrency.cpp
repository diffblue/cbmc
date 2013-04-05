/*******************************************************************\

Module: Add constraints to equation encoding partial orders on events

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#include <i2string.h>
#include <arith_tools.h>

#include "partial_order_concurrency.h"

/*******************************************************************\

Function: partial_order_concurrencyt::~partial_order_concurrencyt

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

partial_order_concurrencyt::partial_order_concurrencyt()
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

Function: partial_order_concurrencyt::clock

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt partial_order_concurrencyt::clock(event_it event)
{
  irep_idt identifier;

  if(event->is_assignment())
    identifier=id2string(id(event))+"$wclk";
  else if(event->is_shared_read())
    identifier=id2string(id(event))+"$rclk";
  else if(event->is_spawn())
    identifier=i2string(event->source.thread_nr+1)+"$spwnclk";
  else
    assert(false);

  return symbol_exprt(identifier, clock_type);
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

Function: partial_order_concurrencyt::po_constraint

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

exprt partial_order_concurrencyt::po_constraint(
  event_it e1, event_it e2)
{
  return binary_relation_exprt(clock(e1), ID_lt, clock(e2));
}


#if 0

#include <cassert>
#include <limits>
#include <sstream>

#include <i2string.h>
#include <std_expr.h>
#include <simplify_expr.h>
#include <arith_tools.h>
#include <symbol.h>
#include <solvers/prop/prop_conv.h>

#include "partial_order_concurrency.h"
#include "memory_model.h"
#include "symex_target_equation.h"

/*******************************************************************\

Function: partial_order_concurrencyt::partial_order_concurrencyt

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

partial_order_concurrencyt::partial_order_concurrencyt(
    partial_order_concurrencyt &_memory_model,
    symex_target_equationt &_target,
    const namespacet &_ns,
    messaget &_message):
  memory_model(_memory_model),
  target(_target),
  ns(_ns),
  message(_message),
  prop_var("goto_symex::\\edge#"),
  prop_cnt(0),
  node_type(nil_typet())
{
}

/*******************************************************************\

Function: partial_order_concurrencyt::node_symbol

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt partial_order_concurrencyt::node_symbol(
    const evtt &evt,
    const std::string &prefix) const
{
  assert(!node_type.is_nil());
  assert(evt.direction==evtt::D_READ ||
      evt.direction==evtt::D_WRITE);

  std::string name=prefix+"$"+id2string(evt.address)+"$";
  name+=evt.value.id()==ID_symbol ?
    id2string(to_symbol_expr(evt.value).get_identifier()) :
    "initval";

  return symbol_exprt(name, node_type);
}

/*******************************************************************\

Function: partial_order_concurrencyt::check_to_string

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

std::string partial_order_concurrencyt::check_to_string(const acyclict check)
{
  switch(check)
  {
    case AC_UNIPROC: return "uniproc";
    case AC_THINAIR: return "thinair";
    case AC_GHB: return "ghb";
    case AC_PPC_WS_FENCE: return "ppc_ws_fence";
    case AC_N_AXIOMS: assert(false);
  }

  assert(false);
  return "";
}

/*******************************************************************\

Function: partial_order_concurrencyt::fresh_nondet_bool

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt partial_order_concurrencyt::fresh_nondet_bool()
{
  return symbol_exprt(prop_var+i2string(prop_cnt++), bool_typet());
}

/*******************************************************************\

Function: partial_order_concurrencyt::clock

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt partial_order_concurrencyt::clock(
    const acyclict check,
    const evtt &n,
    const unsigned step) const
{
  return clock(check, n, step, evtt::D_ISYNC);
}

/*******************************************************************\

Function: partial_order_concurrencyt::clock

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt partial_order_concurrencyt::clock(
    const acyclict check,
    const evtt &n,
    const unsigned step,
    const evtt::event_dirt other_dir) const
{
  std::ostringstream prefix;
  prefix << check_to_string(check);
  if(step!=S_COMMIT)
    prefix << "." << step;

  switch(n.direction)
  {
    case evtt::D_READ:
    case evtt::D_WRITE:
      return node_symbol(n, prefix.str());
    case evtt::D_SYNC:
    case evtt::D_LWSYNC:
      prefix << "$" << event_to_string(n);
      if(n.direction==evtt::D_LWSYNC)
        switch(other_dir)
        {
          case evtt::D_READ: prefix << "$r"; break;
          case evtt::D_WRITE: prefix << "$ww"; break;
          case evtt::D_SYNC:
          case evtt::D_LWSYNC:
          case evtt::D_ISYNC:
            assert(false);
            break;
        }
      return symbol_exprt(prefix.str(), node_type);
    case evtt::D_ISYNC:
      assert(false);
  }

  return symbol_exprt();
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_constraint

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_constraint(
    exprt &expr,
    const guardt &guard,
    const symex_targett::sourcet &source,
    const std::string &po_name)
{
  simplify(expr, ns);

  target.constraint(guard, expr, source);

  std::ostringstream os_debug;
  os_debug << "Added " << po_name << " constraint" << std::endl;
  target.SSA_steps.front().output(ns, os_debug);
  message.debug(os_debug.str());

  std::pair<std::map<std::string, unsigned>::iterator, bool> stat_entry=
    num_concurrency_constraints.insert(std::make_pair(po_name, 1));
  if(!stat_entry.second)
    ++(stat_entry.first->second);
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_clock_constraint

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt partial_order_concurrencyt::add_clock_constraint(
    const symbol_exprt &n1_sym,
    const symbol_exprt &n2_sym,
    const symex_targett::sourcet &source,
    const std::string &po_name)
{
  symbol_exprt s=fresh_nondet_bool();

  equal_exprt e(s, binary_relation_exprt(n1_sym, ID_lt, n2_sym));
  add_constraint(e, guardt(), source, po_name);

  return s;
}

/*******************************************************************\

Function: partial_order_concurrencyt::build_partial_order_constraint

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::build_partial_order_constraint(
    const acyclict check,
    const std::string &po_name,
    const evtt &n1,
    const unsigned n1_step,
    const evtt::event_dirt n1_o_d,
    const evtt &n2,
    const unsigned n2_step,
    const evtt::event_dirt n2_o_d,
    symbol_exprt &dest)
{
  symbol_exprt n1_sym=clock(check, n1, n1_step, n1_o_d);
  symbol_exprt n2_sym=clock(check, n2, n2_step, n2_o_d);

  if(n1.atomic_sect_id!=n2.atomic_sect_id)
  {
    if(n1.atomic_sect_id!=0)
    {
      assert(atomic_section_bounds[check].size()>n1.atomic_sect_id);
      n1_sym=atomic_section_bounds[check][n1.atomic_sect_id].second;
      assert(!n1_sym.get_identifier().empty());
    }
    if(n2.atomic_sect_id!=0)
    {
      assert(atomic_section_bounds[check].size()>n2.atomic_sect_id);
      n2_sym=atomic_section_bounds[check][n2.atomic_sect_id].first;
      assert(!n2_sym.get_identifier().empty());
    }
  }

  std::pair<clock_mapt::iterator, bool> entry=clock_constraint_cache.insert(
      std::make_pair(
        std::make_pair(n1_sym.get_identifier(), n2_sym.get_identifier()),
        symbol_exprt()));
  if(entry.second)
    entry.first->second=add_clock_constraint(n1_sym, n2_sym, n2.source, po_name);

  dest=entry.first->second;
}

/*******************************************************************\

Function: partial_order_concurrencyt::get_partial_order_constraint

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

const symbol_exprt &partial_order_concurrencyt::get_partial_order_constraint(
    const acyclict check,
    const std::string &po_name,
    const evtt &n1,
    const unsigned n1_step,
    const evtt::event_dirt n1_o_d,
    const evtt &n2,
    const unsigned n2_step,
    const evtt::event_dirt n2_o_d)
{
  std::pair<pointwise_mapt::iterator, bool> entry=edge_cache[check].insert(
      std::make_pair(std::make_pair(
          std::make_pair(&n1, std::make_pair(n1_step, n1_o_d)),
          std::make_pair(&n2, std::make_pair(n2_step, n2_o_d))), symbol_exprt()));

  if(entry.second)
    build_partial_order_constraint(check, po_name,
        n1, n1_step, n1_o_d, n2, n2_step, n2_o_d, entry.first->second);

  return entry.first->second;
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_partial_order_constraint

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_partial_order_constraint(
    const acyclict check,
    const std::string &po_name,
    const evtt &n1,
    const evtt &n2,
    const exprt &cond)
{
  add_partial_order_constraint(check, po_name,
      n1, S_COMMIT, evtt::D_ISYNC,
      n2, S_COMMIT, evtt::D_ISYNC,
      cond);
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_partial_order_constraint

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_partial_order_constraint(
    const acyclict check,
    const std::string &po_name,
    const evtt &n1,
    const unsigned n1_step,
    const evtt::event_dirt n1_o_d,
    const evtt &n2,
    const unsigned n2_step,
    const evtt::event_dirt n2_o_d,
    const exprt &cond)
{
  if(cond.is_false())
    return;

  const symbol_exprt &lt=
    get_partial_order_constraint(check, po_name,
        n1, n1_step, n1_o_d, n2, n2_step, n2_o_d);

  if(cond.is_true())
    acyclic_constraints[check].push_back(lt);
  else
  {
    implies_exprt i(cond, lt);
    simplify(i, ns);
    acyclic_constraints[check].push_back(i);
  }

  edge_to_guard[check][&n1].push_back(
      std::make_pair(&n2, std::make_pair(cond, po_name)));
}

/*******************************************************************\

Function: partial_order_concurrencyt::event_to_string

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

std::string partial_order_concurrencyt::event_to_string(
    const evtt &evt) const
{
  std::ostringstream oss;

  switch(evt.direction)
  {
    case evtt::D_WRITE:
    case evtt::D_READ:
      evt.print(oss);
      break;
    case evtt::D_SYNC:
    case evtt::D_LWSYNC:
      {
        std::map<evtt const*, unsigned>::const_iterator nr=
          barrier_id.find(&evt);
        assert(nr!=barrier_id.end());
        evt.print(oss);
        oss << "#" << nr->second;
      }
      break;
    case evtt::D_ISYNC:
      assert(false);
      break;
  }

  return oss.str();
}

/*******************************************************************\

Function: partial_order_concurrencyt::print_graph

  Inputs: 

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::print_graph(
    const adj_matrixt &graph,
    const std::string &edge_label,
    namespacet const& ns) const
{
  std::ostringstream os_debug;

  os_debug << "// " << edge_label << "-graph" << std::endl;
  for(adj_matrixt::const_iterator n1=graph.begin();
      n1!=graph.end();
      ++n1)
    for(std::map<evtt const*, exprt>::const_iterator n2=n1->second.begin();
        n2!=n1->second.end();
        ++n2)
      os_debug
        << event_to_string(*(n1->first))
        << " ->  "
        << event_to_string(*(n2->first))
        << " [label=\"" << edge_label << ": "
        << from_expr(ns, "", n2->second) << "\""
        << ((edge_label!="po" && edge_label!="ab") ? ", constraint=false" : "")
        << "];"
        << std::endl;

  message.debug(os_debug.str());
}

/*******************************************************************\

Function: partial_order_concurrencyt::init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::init(
    const abstract_events_in_program_ordert &abstract_events_in_po)
{
  per_thread_evt_no.resize(abstract_events_in_po.size());
  assert(abstract_events_in_po.size()>1);
  assert(!abstract_events_in_po.front().abstract_events.empty());
  assert(abstract_events_in_po.front().abstract_events.front().source.thread_nr==0);

  typedef abstract_events_per_processort::abstract_eventst::const_iterator evt_itt;
  unsigned num_evts=0;

  // add initialisation events to cope with uninitialised globals
  const evtt *first_spawn=0;
  bool before_first_spawn=false;
  if((++abstract_events_in_po.begin())->parent_event)
  {
    first_spawn=(++abstract_events_in_po.begin())->parent_event;
    before_first_spawn=true;
  }

  for(abstract_events_in_program_ordert::const_iterator
      it=abstract_events_in_po.begin();
      it!=abstract_events_in_po.end();
      ++it)
  {
    if(it->abstract_events.empty())
      continue;

    for(evt_itt e_it=it->abstract_events.begin();
        e_it!=it->abstract_events.end();
        ++e_it)
    {
      const evtt &e=*e_it;

      if(before_first_spawn && e.direction==evtt::D_WRITE && e.guard.is_true())
        init_val.insert(std::make_pair(e.address, evtt()));

      if(&e==first_spawn)
        before_first_spawn=false;

      if(e.direction!=evtt::D_READ)
        continue;

      if(init_val.find(e.address)==init_val.end())
      {
        const symbolt &sym=ns.lookup(e.address);
        exprt val=sym.value;
        if(val.is_nil())
        {
          static int init_cnt=0;
          std::string init_name="global_init_dummy$"+i2string(init_cnt++);
          val=symbol_exprt(init_name, sym.type);
        }
        const evtt &i=init_val.insert(std::make_pair(e.address,
              evtt(guardt(),
                symex_targett::sourcet(e.source.pc),
                evtt::D_WRITE, e.address, val, 0, 0))).first->second;

        per_thread_evt_no[0].add_event(i);
        ++num_evts;
        writes_per_address[e.address].push_back(&i);
      }
    }

    assert(!before_first_spawn);
  }

  // collect events
  std::ostringstream os_debug;
  os_debug << "digraph G {" << std::endl << "splines=true;" << std::endl;
  unsigned x=0;
  for(abstract_events_in_program_ordert::const_iterator
      it=abstract_events_in_po.begin();
      it!=abstract_events_in_po.end();
      ++it)
  {
    if(it->abstract_events.empty())
      continue;

    x+=1000;
    unsigned y=0;
    const unsigned thread_nr=it->abstract_events.front().source.thread_nr;
    assert(thread_nr>=0 && thread_nr<abstract_events_in_po.size());
    numbered_evtst &thread_evts=per_thread_evt_no[thread_nr];
    if(it->parent_event)
    {
      assert(it->parent_event->source.thread_nr<thread_nr);
      const numbered_evtst &parent_map=
        per_thread_evt_no[it->parent_event->source.thread_nr];
      numbered_evtst::const_iterator parent_entry=
        parent_map.find(*(it->parent_event));
      assert(parent_entry!=parent_map.end());
      thread_evts.add_events(parent_map.begin(), parent_entry+1);
      y=300*(parent_entry+1-parent_map.begin());
    }

    for(evt_itt e_it=it->abstract_events.begin();
        e_it!=it->abstract_events.end();
        ++e_it)
    {
      const evtt &e=*e_it;
      assert(e.source.thread_nr==thread_nr);
      thread_evts.add_event(e);
      num_evts+=memory_model.steps_per_event(*this, e.direction);
      switch(e.direction)
      {
        case evtt::D_WRITE:
          writes_per_address[e.address].push_back(&e);
          break;
        case evtt::D_READ:
          reads_per_address[e.address].push_back(&e);
          break;
        case evtt::D_LWSYNC:
        case evtt::D_SYNC:
          barrier_id.insert(std::make_pair(&e, barrier_id.size()));
          break;
        case evtt::D_ISYNC:
          break;
      }

      if(e.direction!=evtt::D_ISYNC)
      {
        os_debug
          << event_to_string(e)
          << " [pos=\"" << x << ",-" << y << "\"];" << std::endl;
          y+=300;
      }
    }
  }

  for(per_address_mapt::const_iterator w_it=writes_per_address.begin();
      w_it!=writes_per_address.end();
      ++w_it)
    os_debug << "Writes to " << w_it->first << ": "
      << w_it->second.size() << std::endl;
  for(per_address_mapt::const_iterator r_it=reads_per_address.begin();
      r_it!=reads_per_address.end();
      ++r_it)
    os_debug << "Reads from " << r_it->first << ": "
      << r_it->second.size() << std::endl;

  message.debug(os_debug.str());

  per_address_mapt::size_type relevant_writes=0;
  for(per_address_mapt::const_iterator w_it=writes_per_address.begin();
      w_it!=writes_per_address.end();
      ++w_it)
    if(reads_per_address.find(w_it->first)!=reads_per_address.end())
      ++relevant_writes;
  num_concurrency_constraints["num-unique-addresses"]=
    std::max(relevant_writes, reads_per_address.size());
  unsigned max_per_addr=0;
  for(per_address_mapt::const_iterator w_it=writes_per_address.begin();
      w_it!=writes_per_address.end();
      ++w_it)
    if(w_it->second.size()>max_per_addr)
      max_per_addr=w_it->second.size();
  for(per_address_mapt::const_iterator r_it=reads_per_address.begin();
      r_it!=reads_per_address.end();
      ++r_it)
    if(r_it->second.size()>max_per_addr)
      max_per_addr=r_it->second.size();
  num_concurrency_constraints["max-per-address"]=max_per_addr;

  // prepare the mapping between events and (symbolic) integers
  num_concurrency_constraints["tot-subevent-count"]=num_evts;
  mp_integer width=address_bits(num_evts);
  assert(width<std::numeric_limits<unsigned>::max());
  node_type=unsignedbv_typet(integer2long(width));

  // if memory model uses sub clocks, add event-internal constraints
  memory_model.add_sub_clock_rules(*this);
}

/*******************************************************************\

Function: partial_order_concurrencyt::first_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const abstract_eventt* partial_order_concurrencyt::first_of(
    const evtt &e1,
    const evtt &e2) const
{
  if(e1.source.thread_nr==e2.source.thread_nr)
  {
    if(per_thread_evt_no[e1.source.thread_nr].find(e1)<
        per_thread_evt_no[e1.source.thread_nr].find(e2))
      return &e1;
    else
      return &e2;
  }
  else if(e1.source.thread_nr<e2.source.thread_nr)
  {
    if(per_thread_evt_no[e2.source.thread_nr].find(e1)!=
        per_thread_evt_no[e2.source.thread_nr].end())
      return &e1;
  }
  else
  {
    if(per_thread_evt_no[e1.source.thread_nr].find(e2)!=
        per_thread_evt_no[e1.source.thread_nr].end())
      return &e2;
  }

  return 0;
}

/*******************************************************************\

Function: partial_order_concurrencyt::get_thread

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const numbered_evtst& partial_order_concurrencyt::get_thread(
    const evtt &e) const
{
  const unsigned thread_nr=e.source.thread_nr;
  assert(thread_nr<per_thread_evt_no.size());
  return per_thread_evt_no[thread_nr];
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_atomic_sections

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_atomic_sections(const acyclict check)
{
  for(numbered_per_thread_evtst::const_iterator it=per_thread_evt_no.begin();
      it!=per_thread_evt_no.end();
      ++it)
  {
    // we assume that only a single atomic section is live at any time; otherwise
    // a map from atomic section ids to per_address_mapt would be required
    unsigned current_atomic_sect=0;
    symbol_exprt preceding_node_in_a_s;
    preceding_node_in_a_s.make_nil();

    for(numbered_evtst::const_iterator e_it=it->begin();
        e_it!=it->end();
        ++e_it)
    {
      const evtt &e=**e_it;

      if(e.atomic_sect_id!=current_atomic_sect)
      {
        current_atomic_sect=e.atomic_sect_id;
        preceding_node_in_a_s.make_nil();
      }

      if(current_atomic_sect!=0)
      {
        symbol_exprt node_sym;
        node_sym.make_nil();

        switch(e.direction)
        {
          case evtt::D_READ:
          case evtt::D_WRITE:
          case evtt::D_SYNC:
            node_sym=clock(check, e, S_COMMIT);
            break;
          case evtt::D_LWSYNC:
            node_sym=clock(check, e, S_COMMIT, evtt::D_WRITE);
            {
              symbol_exprt node_sym_r=clock(check, e, S_COMMIT, evtt::D_READ);
              equal_exprt eq(node_sym, node_sym_r);
              add_constraint(eq, guardt(), e.source, "atomic-block");
            }
            break;
          case evtt::D_ISYNC:
            break;
        }

        if(!preceding_node_in_a_s.is_nil() &&
            !node_sym.is_nil())
        {
          equal_exprt eq(plus_exprt(preceding_node_in_a_s,
                from_integer(1, node_type)),
              node_sym);
          add_constraint(eq, guardt(), e.source, "atomic-block");
        }

        if(!node_sym.is_nil())
        {
          if(atomic_section_bounds[check].size()<=current_atomic_sect)
            atomic_section_bounds[check].resize(current_atomic_sect+1);

          if(preceding_node_in_a_s.is_nil())
            atomic_section_bounds[check][current_atomic_sect].first=node_sym;

          atomic_section_bounds[check][current_atomic_sect].second=
            node_sym;

          preceding_node_in_a_s.swap(node_sym);
        }
      }
    }
  }
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_atomic_sections

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_atomic_sections()
{
  memory_model.add_atomic_sections(*this);
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_program_order

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_program_order(adj_matricest &po)
{
  for(numbered_per_thread_evtst::const_iterator it=per_thread_evt_no.begin();
      it!=per_thread_evt_no.end();
      ++it)
    if(it->begin()!=it->end())
      memory_model.add_program_order(*this, *it, po);

  print_graph(po[AC_GHB], "po", ns);
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_read_from

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_read_from(
    adj_matricest &rf)
{
  for(per_address_mapt::const_iterator r_it=reads_per_address.begin();
      r_it!=reads_per_address.end();
      ++r_it)
  {
    per_address_mapt::const_iterator w_it=writes_per_address.find(r_it->first);
    assert(w_it!=writes_per_address.end()); // at least the init event

    memory_model.add_read_from(*this, r_it->second, w_it->second, rf);
  }

  print_graph(rf[AC_GHB], "rf", ns);
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_write_serialisation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_write_serialisation(
    adj_matricest &ws)
{
  for(numbered_per_thread_evtst::const_iterator it=per_thread_evt_no.begin();
      it!=per_thread_evt_no.end();
      ++it)
    if(it->begin()!=it->end())
      memory_model.add_write_serialisation_internal(
          *this, *it, reads_per_address, ws);

  for(per_address_mapt::const_iterator w_it=writes_per_address.begin();
      w_it!=writes_per_address.end();
      ++w_it)
    if(reads_per_address.find(w_it->first)!=reads_per_address.end())
      memory_model.add_write_serialisation_external(*this, w_it->second, ws);

  print_graph(ws[AC_GHB], "ws", ns);
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_from_read

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_from_read(
    const adj_matricest &rf,
    const adj_matricest &ws,
    adj_matricest &fr)
{
  memory_model.add_from_read(*this, rf, ws, fr);

  print_graph(fr[AC_GHB], "fr", ns);
}

/*******************************************************************\

Function: partial_order_concurrencyt::add_barriers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::add_barriers(
    const adj_matricest &rf,
    const adj_matricest &ws,
    const adj_matricest &fr)
{
  adj_matricest ab;

  for(numbered_per_thread_evtst::const_iterator it=per_thread_evt_no.begin();
      it!=per_thread_evt_no.end();
      ++it)
    if(it->begin()!=it->end())
      memory_model.add_barriers(*this, *it, rf, ws, fr, ab);

  print_graph(ab[AC_GHB], "ab", ns);
}

/*******************************************************************\

Function: partial_order_concurrencyt::acyclic

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partial_order_concurrencyt::acyclic()
{
  for(unsigned i=0; i<AC_N_AXIOMS; ++i)
  {
    if(acyclic_constraints[i].empty())
      continue;

    and_exprt a;
    exprt::operandst op(acyclic_constraints[i].size());

    std::list<exprt>::iterator l_it=acyclic_constraints[i].begin();
    Forall_expr(it, op)
    {
      it->swap(*l_it);
      ++l_it;
    }

    a.operands().swap(op);
    target.constraint(guardt(), a, symex_targett::sourcet());
  }

  // complete dot graph
  message.debug("}");
}

#endif
