/*******************************************************************\

Module: Strategies for picking the abstract events to instrument

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// Strategies for picking the abstract events to instrument

#include "goto2graph.h"

#include <string>
#include <fstream>

#ifdef HAVE_GLPK
#include <glpk.h>
#include <cstdlib>
#endif

void instrumentert::instrument_with_strategy(instrumentation_strategyt strategy)
{
  var_to_instr.clear();
  id2loc.clear();
  id2cycloc.clear();

  if(!set_of_cycles.empty())
  {
    switch(strategy)
    {
      case all:
        instrument_all_inserter(set_of_cycles);
        break;
      case one_event_per_cycle:
        instrument_one_event_per_cycle_inserter(set_of_cycles);
        break;
      case min_interference:
        instrument_minimum_interference_inserter(set_of_cycles);
        break;
      case read_first:
        instrument_one_read_per_cycle_inserter(set_of_cycles);
        break;
      case write_first:
        instrument_one_write_per_cycle_inserter(set_of_cycles);
        break;
      case my_events:
        assert(false);
    }
  }
  else if(num_sccs!=0)
  {
    for(std::size_t i=0; i<num_sccs; ++i)
    {
      switch(strategy)
      {
        case all:
          instrument_all_inserter(set_of_cycles_per_SCC[i]);
          break;
        case one_event_per_cycle:
          instrument_one_event_per_cycle_inserter(set_of_cycles_per_SCC[i]);
          break;
        case min_interference:
          instrument_minimum_interference_inserter(set_of_cycles_per_SCC[i]);
          break;
        case read_first:
          instrument_one_read_per_cycle_inserter(set_of_cycles_per_SCC[i]);
          break;
        case write_first:
          instrument_one_write_per_cycle_inserter(set_of_cycles_per_SCC[i]);
          break;
        case my_events:
          assert(false);
      }
    }
  }
  else
    message.debug() << "no cycles to instrument" << messaget::eom;
}

void inline instrumentert::instrument_all_inserter(
  const std::set<event_grapht::critical_cyclet> &subset_of_cycles)
{
  for(std::set<event_grapht::critical_cyclet>::const_iterator it =
        subset_of_cycles.begin();
      it != subset_of_cycles.end();
      ++it)
  {
    for(std::set<event_grapht::critical_cyclet::delayt>::const_iterator
      p_it=it->unsafe_pairs.begin();
      p_it!=it->unsafe_pairs.end(); ++p_it)
    {
      const abstract_eventt &first_ev=egraph[p_it->first];
      var_to_instr.insert(first_ev.variable);
      id2loc.insert(
        std::pair<irep_idt, source_locationt>(
          first_ev.variable, first_ev.source_location));
      if(!p_it->is_po)
      {
        const abstract_eventt &second_ev = egraph[p_it->second];
        var_to_instr.insert(second_ev.variable);
        id2loc.insert(
          std::pair<irep_idt, source_locationt>(
            second_ev.variable, second_ev.source_location));
      }
    }
  }
}

void inline instrumentert::instrument_one_event_per_cycle_inserter(
  const std::set<event_grapht::critical_cyclet> &subset_of_cycles)
{
  /* to keep track of the delayed pair, and to avoid the instrumentation
     of two pairs in a same cycle */
  std::set<event_grapht::critical_cyclet::delayt> delayed;

  for(std::set<event_grapht::critical_cyclet>::iterator it =
        subset_of_cycles.begin();
      it != subset_of_cycles.end();
      ++it)
  {
    /* cycle with already a delayed pair? */
    bool next=false;
    for(std::set<event_grapht::critical_cyclet::delayt>::iterator
      p_it=it->unsafe_pairs.begin();
      p_it!=it->unsafe_pairs.end(); ++p_it)
    {
      if(delayed.find(*p_it)!=delayed.end())
      {
        next=true;
        break;
      }
    }

    if(next)
      continue;

    /* instruments the first pair */
    if(!it->unsafe_pairs.empty())
    {
      std::set<event_grapht::critical_cyclet::delayt>::iterator
        p_it=it->unsafe_pairs.begin();
      delayed.insert(*p_it);
      const abstract_eventt &first_ev=egraph[p_it->first];
      var_to_instr.insert(first_ev.variable);
      id2loc.insert(
        std::pair<irep_idt, source_locationt>(
          first_ev.variable, first_ev.source_location));
      if(!p_it->is_po)
      {
        const abstract_eventt &second_ev=egraph[p_it->second];
        var_to_instr.insert(second_ev.variable);
        id2loc.insert(
          std::pair<irep_idt, source_locationt>(
            second_ev.variable, second_ev.source_location));
      }
    }
  }
}

void inline instrumentert::instrument_one_read_per_cycle_inserter(
  const std::set<event_grapht::critical_cyclet> &)
{
  /* TODO */
  throw "read first strategy not implemented yet";
}

void inline instrumentert::instrument_one_write_per_cycle_inserter(
  const std::set<event_grapht::critical_cyclet> &)
{
  /* TODO */
  throw "write first strategy not implemented yet";
}

/// cost function
unsigned inline instrumentert::cost(
  const event_grapht::critical_cyclet::delayt &e)
{
  /* cost(poW*)=1
     cost(poRW)=cost(rfe)=2
     cost(poRR)=3 */
  if(egraph[e.first].operation==abstract_eventt::operationt::Write)
    return 1;
  else if(egraph[e.second].operation==abstract_eventt::operationt::Write
    || !e.is_po)
    return 2;
  else
    return 3;
}

void inline instrumentert::instrument_minimum_interference_inserter(
  const std::set<event_grapht::critical_cyclet> &subset_of_cycles)
{
  /* Idea:
     We solve this by a linear programming approach,
     using for instance glpk lib.

     Input: the edges to instrument E, the cycles C_j
     Pb: min sum_{e_i in E} d(e_i).x_i
         s.t. for all j, sum_{e_i in C_j} >= 1,
       where e_i is a pair to potentially instrument,
       x_i is a Boolean stating whether we instrument
       e_i, and d() is the cost of an instrumentation.
     Output: the x_i, saying which pairs to instrument

     For this instrumentation, we propose:
     d(poW*)=1
     d(poRW)=d(rfe)=2
     d(poRR)=3

     This function can be refined with the actual times
     we get in experimenting the different pairs in a
     single IRIW.
  */

#ifdef HAVE_GLPK
  /* first, identify all the unsafe pairs */
  std::set<event_grapht::critical_cyclet::delayt> edges;
  for(std::set<event_grapht::critical_cyclet>::iterator C_j =
        subset_of_cycles.begin();
      C_j != subset_of_cycles.end();
      ++C_j)
    for(std::set<event_grapht::critical_cyclet::delayt>::const_iterator e_i=
      C_j->unsafe_pairs.begin();
      e_i!=C_j->unsafe_pairs.end();
      ++e_i)
      edges.insert(*e_i);

  glp_prob *lp;
  glp_iocp parm;
  glp_init_iocp(&parm);
  parm.msg_lev=GLP_MSG_OFF;
  parm.presolve=GLP_ON;

  lp=glp_create_prob();
  glp_set_prob_name(lp, "instrumentation optimisation");
  glp_set_obj_dir(lp, GLP_MIN);

  message.debug() << "edges: " << edges.size()
                  << " cycles:" << subset_of_cycles.size() << messaget::eom;

  /* sets the variables and coefficients */
  glp_add_cols(lp, edges.size());
  std::size_t i=0;
  for(std::set<event_grapht::critical_cyclet::delayt>::iterator
      e_i=edges.begin();
      e_i!=edges.end();
      ++e_i)
  {
    ++i;
    std::string name="e_"+std::to_string(i);
    glp_set_col_name(lp, i, name.c_str());
    glp_set_col_bnds(lp, i, GLP_LO, 0.0, 0.0);
    glp_set_obj_coef(lp, i, cost(*e_i));
    glp_set_col_kind(lp, i, GLP_BV);
  }

  /* sets the constraints (soundness): one per cycle */
  glp_add_rows(lp, subset_of_cycles.size());
  i=0;
  for(std::set<event_grapht::critical_cyclet>::iterator C_j =
        subset_of_cycles.begin();
      C_j != subset_of_cycles.end();
      ++C_j)
  {
    ++i;
    std::string name="C_"+std::to_string(i);
    glp_set_row_name(lp, i, name.c_str());
    glp_set_row_bnds(lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
  }

  const std::size_t mat_size = subset_of_cycles.size() * edges.size();
  message.debug() << "size of the system: " << mat_size
    << messaget::eom;
  std::vector<int> imat(mat_size+1);
  std::vector<int> jmat(mat_size+1);
  std::vector<double> vmat(mat_size+1);

  /* fills the constraints coeff */
  /* tables read from 1 in glpk -- first row/column ignored */
  std::size_t col=1;
  std::size_t row=1;
  i=1;
  for(std::set<event_grapht::critical_cyclet::delayt>::iterator
    e_i=edges.begin();
    e_i!=edges.end();
    ++e_i)
  {
    row=1;
    for(std::set<event_grapht::critical_cyclet>::iterator C_j =
          subset_of_cycles.begin();
        C_j != subset_of_cycles.end();
        ++C_j)
    {
      imat[i]=row;
      jmat[i]=col;
      if(C_j->unsafe_pairs.find(*e_i)!=C_j->unsafe_pairs.end())
        vmat[i]=1.0;
      else
        vmat[i]=0.0;
      ++i;
      ++row;
    }
    ++col;
  }

#ifdef DEBUG
  for(i=1; i<=mat_size; ++i)
    message.statistics() <<i<<"["<<imat[i]<<","<<jmat[i]<<"]="<<vmat[i]
      << messaget::eom;
#endif

  /* solves MIP by branch-and-cut */
  glp_load_matrix(lp, mat_size, imat, jmat, vmat);
  glp_intopt(lp, &parm);

  /* loads results (x_i) */
  message.statistics() << "minimal cost: " << glp_mip_obj_val(lp)
    << messaget::eom;
  i=0;
  for(std::set<event_grapht::critical_cyclet::delayt>::iterator
    e_i=edges.begin();
    e_i!=edges.end();
    ++e_i)
  {
    ++i;
    if(glp_mip_col_val(lp, i)>=1)
    {
      const abstract_eventt &first_ev=egraph[e_i->first];
      var_to_instr.insert(first_ev.variable);
      id2loc.insert(
        std::pair<irep_idt, source_locationt>(
          first_ev.variable, first_ev.source_location));
      if(!e_i->is_po)
      {
        const abstract_eventt &second_ev=egraph[e_i->second];
        var_to_instr.insert(second_ev.variable);
        id2loc.insert(
          std::pair<irep_idt, source_locationt>(
            second_ev.variable, second_ev.source_location));
      }
    }
  }

  glp_delete_prob(lp);
#else
  (void)subset_of_cycles; // unused parameter
  throw "sorry, minimum interference option requires glpk; "
        "please recompile goto-instrument with glpk";
#endif
}

void inline instrumentert::instrument_my_events_inserter(
  const std::set<event_grapht::critical_cyclet> &set,
  const std::set<event_idt> &my_events)
{
  for(std::set<event_grapht::critical_cyclet>::const_iterator
    it=set.begin();
    it!=set.end(); ++it)
  {
    for(std::set<event_grapht::critical_cyclet::delayt>::const_iterator
      p_it=it->unsafe_pairs.begin();
      p_it!=it->unsafe_pairs.end(); ++p_it)
    {
      if(my_events.find(p_it->first)!=my_events.end())
      {
        const abstract_eventt &first_ev=egraph[p_it->first];
        var_to_instr.insert(first_ev.variable);
        id2loc.insert(
          std::pair<irep_idt, source_locationt>(
            first_ev.variable, first_ev.source_location));
        if(!p_it->is_po && my_events.find(p_it->second)!=my_events.end())
        {
          const abstract_eventt &second_ev=egraph[p_it->second];
          var_to_instr.insert(second_ev.variable);
          id2loc.insert(
            std::pair<irep_idt, source_locationt>(second_ev.variable,
              second_ev.source_location));
        }
      }
    }
  }
}

void instrumentert::instrument_my_events(
  const std::set<event_idt> &my_events)
{
  var_to_instr.clear();
  id2loc.clear();
  id2cycloc.clear();

  if(!set_of_cycles.empty())
    instrument_my_events_inserter(set_of_cycles, my_events);
  else if(num_sccs!=0)
  {
    for(std::size_t i=0; i<num_sccs; ++i)
      instrument_my_events_inserter(set_of_cycles_per_SCC[i], my_events);
  }
  else
    message.debug() << "no cycles to instrument" << messaget::eom;
}

std::set<event_idt> instrumentert::extract_my_events()
{
  std::ifstream file;
  file.open("inst.evt");
  std::set<event_idt> this_set;

  std::size_t size;
  file >> size;

  std::size_t tmp;

  for(std::size_t i=0; i<size; i++)
  {
    file >> tmp;
    this_set.insert(tmp);
  }

  file.close();

  return this_set;
}
