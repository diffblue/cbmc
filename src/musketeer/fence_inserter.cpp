/*******************************************************************\

Module: ILP construction for all cycles and resolution

Author: Vincent Nimal

\*******************************************************************/

#include <util/i2string.h>
#include <util/graph.h>

#include <sstream>
#include <fstream>

#ifdef HAVE_GLPK
#include <glpk.h>
#include <cstdlib>
#endif

#include "fence_inserter.h"
#include "ilp.h"

class abstract_eventt;

/*******************************************************************\

Function: fence_insertert::fence_cost

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned fence_insertert::fence_cost(fence_typet f) const {
  switch(f) {
    case Fence:
      return 3;
    case Lwfence:
      return 2;
    case Dp:
      return 1;
    case Branching:
      return 2;
    case Ctlfence:
      return 1;     
  }
  assert(false);
  return 0;
}

/*******************************************************************\

Function: fence_insertert::compute

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::compute() {
  compute_fence_options();
  instrumenter.message.status() << "Preprocessing" << messaget::eom;
  preprocess();
  instrumenter.message.status() << "Solving" << messaget::eom;
  if(unique>0)
    solve();
  else
    instrumenter.message.result() << "no cycle concerned" << messaget::eom;
}

/*******************************************************************\

Function: fence_insertert::preprocess

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::preprocess() {
  process_cycles_selection();

  cycles_visitor.po_edges(po);

  /* TODO: replace lists by sets and carefully count the number of constraints
     _with_ removing the existing ones (i.e., those which are not inserted) */

  instrumenter.message.status() << "Preparing cycles" << messaget::eom;
  for(std::set<event_grapht::critical_cyclet>::const_iterator
    C_j=instrumenter.set_of_cycles.begin();
    C_j!=instrumenter.set_of_cycles.end();
    ++C_j)
  {
    /* filtering */
    if(filter_cycles(C_j->id)) 
      continue;

    std::set<unsigned> new_wr_set;
    cycles_visitor.powr_constraint(*C_j, new_wr_set);
    powr_constraints.push_back(new_wr_set);

    std::set<unsigned> new_ww_set;
    cycles_visitor.poww_constraint(*C_j, new_ww_set);
    poww_constraints.push_back(new_ww_set);

    std::set<unsigned> new_rw_set;
    cycles_visitor.porw_constraint(*C_j, new_rw_set);
    porw_constraints.push_back(new_rw_set);

    std::set<unsigned> new_rr_set;
    cycles_visitor.porr_constraint(*C_j, new_rr_set);
    porr_constraints.push_back(new_rr_set);

    if(model==Power || model==Unknown) {
      std::set<unsigned> new_comset;
      cycles_visitor.com_constraint(*C_j, new_comset);
      com_constraints.push_back(new_comset);
    }

    assert(powr_constraints.size() == poww_constraints.size());
    assert(poww_constraints.size() == porw_constraints.size());
    assert(porw_constraints.size() == porr_constraints.size());
  }

  // Note: not true if filters
  //assert(non_powr_constraints.size() == instrumenter.set_of_cycles.size());

  // NEW
  /* first, powr constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=powr_constraints.begin();
    e_i!=powr_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_c_it=e_i->begin();
      e_c_it!=e_i->end();
      ++e_c_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_c_it) != map_to_e.end());
      const_graph_visitor.PT(map_to_e.find(*e_c_it)->second, pt_set);
    }
  }

  /* then, poww constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=poww_constraints.begin();
    e_i!=poww_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      const_graph_visitor.PT(map_to_e.find(*e_nc_it)->second, pt_set);
    }
  }

  /* then, porw constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=porw_constraints.begin();
    e_i!=porw_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      const_graph_visitor.PT(map_to_e.find(*e_nc_it)->second, pt_set);
    }
  }

  /* then, porr constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=porr_constraints.begin();
    e_i!=porr_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      const_graph_visitor.PT(map_to_e.find(*e_nc_it)->second, pt_set);
    }
  }

  if(model==Power || model==Unknown)
  {
    /* finally, Power/ARM constraints for Rfes: for all C_j */
    for(std::list<std::set<unsigned> >::const_iterator
      e_i=com_constraints.begin();
      e_i!=com_constraints.end();
      ++e_i)
    {
      /* for all e */
      for(std::set<unsigned>::const_iterator
        e_c_it=e_i->begin();
        e_c_it!=e_i->end();
        ++e_c_it)
      {
        std::set<unsigned> ct_set;
        assert( invisible_var.map_to_e.find(*e_c_it)
          != invisible_var.map_to_e.end());
        const_graph_visitor.CT(invisible_var.map_to_e.find(*e_c_it)->second, 
          ct_set);

        std::set<unsigned> ct_not_powr_set;
        const_graph_visitor.CT_not_powr(
          invisible_var.map_to_e.find(*e_c_it)->second, ct_not_powr_set);
      }
    }
  }
}

/*******************************************************************\

Function: fence_insertert::mip_set_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void inline fence_insertert::mip_set_var(ilpt& ilp, 
  unsigned& i) 
{
#ifdef HAVE_GLPK
  glp_add_cols(ilp.lp, unique*fence_options);
  //unsigned i=1;
  for(; i<=unique*fence_options; i+=fence_options)
  {
    const bool has_cost = 1; //(po_plus.find(i)==po_plus.end());
    /* has_cost == 0 => invisible variable */
    assert(has_cost); // not useful for this problem

    /* computes the sum of the frequencies of the cycles in which
       this event appears, if requested */
    float freq_sum = 0;
    if(with_freq)
    {
      assert(instrumenter.set_of_cycles.size()==freq_table.size());
      freq_sum += epsilon;
      for(std::set<event_grapht::critical_cyclet>::const_iterator
        C_j=instrumenter.set_of_cycles.begin();
        C_j!=instrumenter.set_of_cycles.end();
        ++C_j)
      {
        /* filters */
        if(filter_cycles(C_j->id)) continue;

        /* if(C_j->find( col_to_var(i) )!=C_j->end()) */
        std::list<unsigned>::const_iterator it;
        for(it = C_j->begin(); it!=C_j->end() && col_to_var(i)!=*it; ++it);

        if(it!=C_j->end())
          freq_sum += freq_table[C_j->id];
      }
    }
    else
      freq_sum = 1;

    if(model==Power || model==Unknown) {
      /* dp variable for e */
      const std::string name_dp="dp_"+i2string(i);
      glp_set_col_name(ilp.lp, i, name_dp.c_str());
      glp_set_col_bnds(ilp.lp, i, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(ilp.lp, i, (has_cost?fence_cost(Dp):0)*freq_sum);
      glp_set_col_kind(ilp.lp, i, GLP_BV);

      /* fence variable for e */
      const std::string name_f="f_"+i2string(i);
      glp_set_col_name(ilp.lp, i+1, name_f.c_str());
      glp_set_col_bnds(ilp.lp, i+1, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(ilp.lp, i+1, (has_cost?fence_cost(Fence):0)*freq_sum);
      glp_set_col_kind(ilp.lp, i+1, GLP_BV);

// Note: uncomment for br and cf fences
#if 0
      /* br variable for e */
      const std::string name_br="br_"+i2string(i);
      glp_set_col_name(ilp.lp, i+2, name_br.c_str());
      glp_set_col_bnds(ilp.lp, i+2, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(ilp.lp, i+2, (has_cost?fence_cost(Branching):0)*freq_sum);
      glp_set_col_kind(ilp.lp, i+2, GLP_BV);

      /* cf variable for e */
      const std::string name_cf="cf_"+i2string(i);
      glp_set_col_name(ilp.lp, i+3, name_cf.c_str());
      glp_set_col_bnds(ilp.lp, i+3, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(ilp.lp, i+3, (has_cost?fence_cost(Ctlfence):0)*freq_sum);
      glp_set_col_kind(ilp.lp, i+3, GLP_BV);
#endif

      if(model==Power) {
        /* lwf variable for e */
        const std::string name_lwf="lwf_"+i2string(i);
        glp_set_col_name(ilp.lp, i+2/*4*/, name_lwf.c_str());
        glp_set_col_bnds(ilp.lp, i+2/*4*/, GLP_LO, 0.0, 0.0);
        glp_set_obj_coef(ilp.lp, i+2/*4*/,
          (has_cost?fence_cost(Lwfence):0)*freq_sum);
        glp_set_col_kind(ilp.lp, i+2/*4*/, GLP_BV);
      }
    }
    else {
      /* fence variable for e */
      const std::string name_f="f_"+i2string(i);
      glp_set_col_name(ilp.lp, i, name_f.c_str());
      glp_set_col_bnds(ilp.lp, i, GLP_LO, 0.0, 0.0);
      glp_set_obj_coef(ilp.lp, i, (has_cost?fence_cost(Fence):0)*freq_sum);
      glp_set_col_kind(ilp.lp, i, GLP_BV);
    }
  }
#else
  throw "Sorry, musketeer requires glpk; please recompile\
    musketeer with glpk.";
#endif
}

/*******************************************************************\

Function: fence_insertert::mip_set_cst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void inline fence_insertert::mip_set_cst(ilpt& ilp, unsigned& i)
{
#ifdef HAVE_GLPK
  glp_add_rows(ilp.lp, constraints_number);
  i=1;

  /* first the powr: for all C_j */
  for(
    std::list<std::set<unsigned> >::const_iterator c_wr_it =
      powr_constraints.begin();
    c_wr_it != powr_constraints.end();
    ++c_wr_it)
  {
    /* for all e */
    for(unsigned j=1; j<=c_wr_it->size(); ++j)
    {
      std::string name="C_"+i2string(i)+"_c_wr_"+i2string(j);
      glp_set_row_name(ilp.lp, i, name.c_str());
      glp_set_row_bnds(ilp.lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
      ++i;
    }
  }

  /* then the poww: for all C_j */
  for(
    std::list<std::set<unsigned> >::const_iterator c_ww_it =
      poww_constraints.begin();
    c_ww_it != poww_constraints.end();
    ++c_ww_it)
  {
    /* for all e */
    for(unsigned j=1; j<=c_ww_it->size(); ++j)
    {
      std::string name="C_"+i2string(i)+"_c_ww_"+i2string(j);
      glp_set_row_name(ilp.lp, i, name.c_str());
      glp_set_row_bnds(ilp.lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
      ++i;
    }
  }

  /* then the porw: for all C_j */
  for(
    std::list<std::set<unsigned> >::const_iterator c_rw_it =
      porw_constraints.begin();
    c_rw_it != porw_constraints.end();
    ++c_rw_it)
  {
    /* for all e */
    for(unsigned j=1; j<=c_rw_it->size(); ++j)
    {
      std::string name="C_"+i2string(i)+"_c_rw_"+i2string(j);
      glp_set_row_name(ilp.lp, i, name.c_str());
      glp_set_row_bnds(ilp.lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
      ++i;
    }
  }

  /* and finally the porr: for all C_j */
  for(
    std::list<std::set<unsigned> >::const_iterator c_rr_it =
      porr_constraints.begin();
    c_rr_it != porr_constraints.end();
    ++c_rr_it)
  {
    /* for all e */
    for(unsigned j=1; j<=c_rr_it->size(); ++j)
    {
      std::string name="C_"+i2string(i)+"_c_rr_"+i2string(j);
      glp_set_row_name(ilp.lp, i, name.c_str());
      glp_set_row_bnds(ilp.lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
      ++i;
    }
  }

  if(model==Power || model==Unknown) {
    for(
      std::list<std::set<unsigned> >::const_iterator c_it =
        com_constraints.begin();
      c_it != com_constraints.end();
      ++c_it)
    {
      /* for all e */
      for(unsigned j=1; j<=c_it->size(); ++j)
      {
        std::string name="C_"+i2string(i)+"_c_"+i2string(j);
        glp_set_row_name(ilp.lp, i, name.c_str());
        glp_set_row_bnds(ilp.lp, i, GLP_LO, 1.0, 0.0); /* >= 1*/
        ++i;
      }
    }
  }
#else
  throw "Sorry, musketeer requires glpk; please recompile\
    musketeer with glpk.";
#endif
}

/*******************************************************************\

Function: fence_insertert::mip_fill_matrix

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void inline fence_insertert::mip_fill_matrix(ilpt& ilp, unsigned& i,
  unsigned const_constraints_number, unsigned const_unique)
{
#ifdef HAVE_GLPK
  unsigned col=1;
  unsigned row=1;
  i=1;

  /* first, powr constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=powr_constraints.begin();
    e_i!=powr_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_c_it=e_i->begin();
      e_c_it!=e_i->end();
      ++e_c_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_c_it) != map_to_e.end());
      const_graph_visitor.PT(map_to_e.find(*e_c_it)->second, pt_set);
      /* sum_e' f_e' */
      for(col=1; col<=unique*fence_options; ++col)
      {
        assert(row<=const_constraints_number);
        assert(col<=const_unique*fence_options);
        ilp.imat[i]=row;
        ilp.jmat[i]=col;
        if(model==Power || model==Unknown) {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
              && col_to_fence(col)==Fence)
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        else {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
            && col_to_fence(col)==Fence)
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        ++i;
      }
      ++row;
    }
  }

  /* then, poww constraints: for all C_j */ 
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=poww_constraints.begin();
    e_i!=poww_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      const_graph_visitor.PT(map_to_e.find(*e_nc_it)->second, pt_set);
      /* sum_e' (f_e' + lwf_e') */
      for(col=1; col<=unique*fence_options; ++col)
      {
        assert(row<=const_constraints_number);
        assert(col<=const_unique*fence_options);
        ilp.imat[i]=row;
        ilp.jmat[i]=col;
        if(model==Power) {
          if(pt_set.find(col_to_var(col))!=pt_set.end() 
              && (col_to_fence(col)==Lwfence || col_to_fence(col)==Fence))
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        else {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
            && col_to_fence(col)==Fence)
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        ++i;
      }
      ++row;
    }
  }

  /* then, porw constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=porw_constraints.begin();
    e_i!=porw_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      const_graph_visitor.PT(map_to_e.find(*e_nc_it)->second, pt_set);
      /* dp_e + sum_e' (f_e' + lwf_e' + br_e') */
      for(col=1; col<=unique*fence_options; ++col)
      {
        assert(row<=const_constraints_number);
        assert(col<=const_unique*fence_options);
        ilp.imat[i]=row;
        ilp.jmat[i]=col;
        if(model==Power) {
          if(col==var_fence_to_col(Dp, *e_nc_it)
              ||(pt_set.find(col_to_var(col))!=pt_set.end()
              && (col_to_fence(col)==Lwfence 
                || col_to_fence(col)==Fence
#if 0
                || col_to_fence(col)==Branching
#endif
              ))
            )
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        else if (model==Unknown) {
          if(col==var_fence_to_col(Dp, *e_nc_it)
              ||(pt_set.find(col_to_var(col))!=pt_set.end()
              && (col_to_fence(col)==Fence 
#if 0
                || col_to_fence(col)==Branching
#endif
              ))
            )
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        else {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
            && (col_to_fence(col)==Fence
#if 0
              || col_to_fence(col)==Branching
#endif
            ))
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        ++i;
      }
      ++row;
    }
  }

  /* then, porr constraints: for all C_j */
  for(std::list<std::set<unsigned> >::const_iterator
    e_i=porr_constraints.begin();
    e_i!=porr_constraints.end();
    ++e_i)
  {
    /* for all e */
    for(std::set<unsigned>::const_iterator
      e_nc_it=e_i->begin();
      e_nc_it!=e_i->end();
      ++e_nc_it)
    {
      std::set<unsigned> pt_set;
      assert(map_to_e.find(*e_nc_it) != map_to_e.end());
      const_graph_visitor.PT(map_to_e.find(*e_nc_it)->second, pt_set);
// uncomment for cf
#if 0
      std::set<unsigned> it_set;
      IT(map_to_e.find(*e_nc_it)->second, it_set);
#endif
      /* dp_e + sum_e' (f_e' + lwf_e') + sum_e'' cf_e'') */
      for(col=1; col<=unique*fence_options; ++col)
      {
        assert(row<=const_constraints_number);
        assert(col<=const_unique*fence_options);
        ilp.imat[i]=row;
        ilp.jmat[i]=col;
        if(model==Power) {
          if(col==var_fence_to_col(Dp, *e_nc_it)
              ||(pt_set.find(col_to_var(col))!=pt_set.end()
              && (col_to_fence(col)==Lwfence
                || col_to_fence(col)==Fence
              ))
#if 0
              ||(it_set.find(col_to_var(col))!=it_set.end()
              && col_to_fence(col)==Ctlfence)
#endif
            )
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        else if (model==Unknown) {
          if(col==var_fence_to_col(Dp, *e_nc_it)
              ||(pt_set.find(col_to_var(col))!=pt_set.end()
              && (col_to_fence(col)==Fence
              ))
#if 0
              ||(it_set.find(col_to_var(col))!=it_set.end()
              && col_to_fence(col)==Ctlfence)
#endif   
            )
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        else {
          if(pt_set.find(col_to_var(col))!=pt_set.end()
            && (col_to_fence(col)==Fence
            ))
            ilp.vmat[i]=1.0;
          else
            ilp.vmat[i]=0.0;
        }
        ++i;
      }
      ++row;
    }
  }

  if(model==Power || model==Unknown) 
  {
    /* finally, Power/ARM constraints for Rfes: for all C_j */
    for(std::list<std::set<unsigned> >::const_iterator
      e_i=com_constraints.begin();
      e_i!=com_constraints.end();
      ++e_i)
    {
      /* for all e */
      for(std::set<unsigned>::const_iterator
        e_c_it=e_i->begin();
        e_c_it!=e_i->end();
        ++e_c_it)
      {
        unsigned possibilities_met=0;

        std::set<unsigned> ct_set;
        assert( invisible_var.map_to_e.find(*e_c_it)
          != invisible_var.map_to_e.end());
        const_graph_visitor.CT(invisible_var.map_to_e.find(*e_c_it)->second, 
          ct_set);

        std::set<unsigned> ct_not_powr_set;
        const_graph_visitor.CT_not_powr(invisible_var.map_to_e.find(
          *e_c_it)->second, ct_not_powr_set);

        instrumenter.message.statistics() << "size of CT for " 
          << invisible_var.map_to_e.find(*e_c_it)->second.first << ","
          << invisible_var.map_to_e.find(*e_c_it)->second.second << ": " 
          << ct_set.size() << messaget::eom;

        /* sum_e' f_e' + sum_e'' lwf_e'' */
        for(col=1; col<=unique*fence_options; ++col)
        {
          assert(row<=const_constraints_number);
          assert(col<=const_unique*fence_options);
          ilp.imat[i]=row;
          ilp.jmat[i]=col;
          if( (ct_set.find(col_to_var(col))!=ct_set.end()
            && col_to_fence(col)==Fence)
            || (ct_not_powr_set.find(col_to_var(col))!=ct_not_powr_set.end()
              && col_to_fence(col)==Lwfence) )
          {
            ilp.vmat[i]=1.0;
            ++possibilities_met;
          }
          else
            ilp.vmat[i]=0.0;
          ++i;
        }
        ++row;
        assert(possibilities_met);
      }
    }
  }
  instrumenter.message.debug() << "3: " << i << " row: " << row 
    << messaget::eom;
#else
  throw "Sorry, musketeer requires glpk; please recompile\
    musketeer with glpk.";
#endif
}

/*******************************************************************\

Function: fence_insertert::solve()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::solve() {
#ifdef HAVE_GLPK
  ilpt ilp;

  instrumenter.message.statistics() << "po^+ edges considered:"
    << unique << " cycles:" << instrumenter.set_of_cycles.size() 
    << messaget::eom;

  /* sets the variables and coefficients */
  //nb of po+ considered * types of fences (_e)
  unsigned i=1;
  mip_set_var(ilp, i);

  /* sets the constraints */
  mip_set_cst(ilp, i);

  instrumenter.message.debug() << "3: " << i << messaget::eom;
  assert(i-1==constraints_number);

  const unsigned const_constraints_number=constraints_number;
  const unsigned const_unique=unique;
 
  const unsigned mat_size=const_unique*fence_options*const_constraints_number;
  instrumenter.message.statistics() << "size of the system: " << mat_size
    << messaget::eom;
  instrumenter.message.statistics() << "# of constraints: " 
    << const_constraints_number << messaget::eom;
  instrumenter.message.statistics() << "# of variables: " 
    << const_unique*fence_options << messaget::eom;

  ilp.set_size(mat_size);

#ifdef DEBUG
  print_vars();
#endif

  /* fills the constraints coeff */
  /* tables read from 1 in glpk -- first row/column ignored */
  mip_fill_matrix(ilp, i, const_constraints_number, const_unique);

  instrumenter.message.statistics() << "i: " << i << " mat_size: " << mat_size 
    << messaget::eom;
  //assert(i-1==mat_size);

#ifdef DEBUG
  for(i=1; i<=mat_size; ++i)
    instrumenter.message.debug() << i << "[" << ilp.imat[i] << "," 
      << ilp.jmat[i] << "]=" << ilp.vmat[i] << messaget::eom;
#endif

  /* solves MIP by branch-and-cut */
  ilp.solve();

#ifdef DEBUG
  print_vars();
#endif

  /* checks optimality */
  switch(glp_mip_status(ilp.lp)) {
    case GLP_OPT:
      instrumenter.message.result() << "Optimal solution found" 
        << messaget::eom;
      break;
    case GLP_UNDEF:
      instrumenter.message.result() << "Solution undefined" << messaget::eom;
      assert(0);
    case GLP_FEAS:
      instrumenter.message.result() << "Solution feasible, yet not proven \
        optimal, due to early termination" << messaget::eom;
      break;
    case GLP_NOFEAS:
      instrumenter.message.result() 
        << "No feasible solution, the system is UNSAT" << messaget::eom;
      assert(0);
  }

  event_grapht& egraph=instrumenter.egraph;

  /* loads results (x_i) */
  instrumenter.message.statistics() << "minimal cost: " 
    << glp_mip_obj_val(ilp.lp) << messaget::eom;
  for(unsigned j=1; j<=const_unique*fence_options; ++j)
  {
    if(glp_mip_col_val(ilp.lp, j)>=1)
    {
      /* insert that fence */
      assert(map_to_e.find(col_to_var(j))!=map_to_e.end());
      const edget& delay = map_to_e.find(col_to_var(j))->second;
      instrumenter.message.statistics() << delay.first << " -> " 
        << delay.second << " : " << to_string(col_to_fence(j)) 
        << messaget::eom;
      instrumenter.message.statistics() << "(between " 
        << egraph[delay.first].source_location << " and "
        << egraph[delay.second].source_location << messaget::eom;
      fenced_edges.insert(std::pair<edget,fence_typet>(delay, col_to_fence(j)));
    }
  }
#else
  throw "Sorry, musketeer requires glpk; please recompile\
    musketeer with glpk.";
#endif
}

/*******************************************************************\

Function: fence_insertert::import_freq

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::import_freq() {
  /* TODO */
}

/*******************************************************************\

Function: fence_insertert::print_to_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::print_to_file()
{
  /* removes redundant (due to several call to the same fenced function) */
  std::set<std::string> non_redundant_display;
  for(std::map<edget,fence_typet>::const_iterator it=fenced_edges.begin();
    it!=fenced_edges.end();
    ++it)
  {
    std::ostringstream s;
    const abstract_eventt& first=instrumenter.egraph[it->first.first];

    s << to_string(it->second) << "|" << first.source_location.get_file() 
      << "|" << first.source_location.get_line() << "|" 
      << first.source_location.get_column() << std::endl;
    non_redundant_display.insert(s.str());
  }

  std::ofstream results;
  results.open("results.txt");
  for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
    it!=non_redundant_display.end();
    ++it)
    results << *it;
  results.close();
}

/*******************************************************************\

Function: fence_insertert::print_to_file_2

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

  /* prints final results */
  void fence_insertert::print_to_file_2() 
  {
    /* removes redundant (due to several call to the same fenced function) */
    std::set<std::string> non_redundant_display;
    for(std::map<edget,fence_typet>::const_iterator it=fenced_edges.begin();
      it!=fenced_edges.end();
      ++it)
    {
      std::ostringstream s;
      const abstract_eventt& first=instrumenter.egraph[it->first.first];
      const abstract_eventt& second=instrumenter.egraph[it->first.second];

      s << to_string(it->second) << "|" << first.source_location.get_file() 
      << "|" << first.source_location.get_line() << "|" 
      << second.source_location.get_file()
      << "|" << second.source_location.get_line() << std::endl;
      non_redundant_display.insert(s.str());
    }
    
    std::ofstream results;
    results.open("results.txt");
    for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
      it!=non_redundant_display.end();
      ++it)
      results << *it;
    results.close();
  }

/*******************************************************************\

Function: fence_insertert::print_to_file_3

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

/* prints final results */
  void fence_insertert::print_to_file_3()
  {
    /* removes redundant (due to several call to the same fenced function) */
    std::set<std::string> non_redundant_display;
    for(std::map<edget,fence_typet>::const_iterator it=fenced_edges.begin();
      it!=fenced_edges.end();
      ++it)
    {
      std::ostringstream s;
      const abstract_eventt& first=instrumenter.egraph[it->first.first];
      const abstract_eventt& second=instrumenter.egraph[it->first.second];

      try {
      s << to_string(it->second) << "|" << first.source_location.get_file() 
        << "|" << first.source_location.get_function() << "|" 
        << first.source_location.get_line() << "|" << first.variable << "|"
        << second.source_location.get_file() << "|"
        << second.source_location.get_function() << "|" 
        << second.source_location.get_line()
        << "|" << second.variable << std::endl;
      non_redundant_display.insert(s.str());
      }
      catch (std::string s) {
        instrumenter.message.warning() 
          << "Couldn't retrieve symbols of variables " << first.variable
          << " and " << second.variable << " due to " << s << messaget::eom;
      }
    }

    std::ofstream results;
    results.open("results.txt");
    for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
      it!=non_redundant_display.end();
      ++it)
      results << *it;
    results.close();
  }

/*******************************************************************\

Function: fence_insertert::print_to_file_4

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

  /* prints final results */
  void fence_insertert::print_to_file_4()
  {
    /* removes redundant (due to several call to the same fenced function) */
    std::set<std::string> non_redundant_display;
    for(std::map<edget,fence_typet>::const_iterator it=fenced_edges.begin();
      it!=fenced_edges.end();
      ++it)
    {
      std::ostringstream s;
      const abstract_eventt& first=instrumenter.egraph[it->first.first];
      const abstract_eventt& second=instrumenter.egraph[it->first.second];

      try {
      s << to_string(it->second) << "|" << first.source_location.get_file() 
        << "|" << first.source_location.get_function() << "|" 
        << first.source_location.get_line() 
        << "|" << first.variable << "|" 
        << get_type(first.variable).get("#c_type") << "|"
        << second.source_location.get_file() << "|" 
        << second.source_location.get_function() << "|" 
        << second.source_location.get_line() 
        << "|" << second.variable << "|"
        << get_type(second.variable).get("#c_type") << std::endl;
      non_redundant_display.insert(s.str());
      }
      catch (std::string s) {
        instrumenter.message.warning() 
          << "Couldn't retrieve types of variables " << first.variable
          << " and " << second.variable << " due to " << s << messaget::eom;
      }
    }

    std::ofstream results;
    results.open("results.txt");
    for(std::set<std::string>::const_iterator it=non_redundant_display.begin();
      it!=non_redundant_display.end();
      ++it)
      results << *it;
    results.close();
  }

/*******************************************************************\

Function: fence_insertert::to_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string fence_insertert::to_string(fence_typet f) const {
  switch(f) {
    case Fence: return "fence";
    case Lwfence: return "lwfence";
    case Dp: return "dp";
    case Branching: return "branching";
    case Ctlfence: return "ctlfence";
  }
  assert (0);
}

/*******************************************************************\

Function: fence_inserter::col_to_var

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline unsigned fence_insertert::col_to_var(unsigned u) const
{
  return (u-u%fence_options)/fence_options+(u%fence_options!=0?1:0);
}

/*******************************************************************\

Function: fence_insertert::col_to_fence

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline fence_insertert::fence_typet fence_insertert::col_to_fence(unsigned u) 
  const
{
  switch(u%fence_options) {
    case 0: return Fence;
    case 1: return Dp;
    case 2: return Lwfence;
    case 3: return Branching;
    case 4: return Ctlfence;
  }
  assert(0);
}

/*******************************************************************\

Function: fence_insertert::var_fence_to_col

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline unsigned fence_insertert::var_fence_to_col(fence_typet f, unsigned var)
  const
{
  switch(f) {
    case Fence: return var*fence_options;
    case Dp: return (var-1)*fence_options+1;
    case Lwfence: return (var-1)*fence_options+2;
    case Branching: return (var-1)*fence_options+3;
    case Ctlfence: return (var-1)*fence_options+4;
  }
  assert(0);
}

/*******************************************************************\

Function: fence_insertert::compute_fence_options

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::compute_fence_options()
{
  switch(model) {
    case TSO:
    case PSO:
    case RMO:
      fence_options = 1; // 2: f, br
      break;
    case Power:
      fence_options = 3; // 5: f, lwf, dp, cf, br
      break;
    case Unknown: /* including ARM */
      fence_options = 2; // 4: f, dp, cf, br
      break;
  }
}

/*******************************************************************\

Function: fence_insertert::print_vars

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void fence_insertert::print_vars() const {
  instrumenter.message.statistics()
    << "---- pos/pos+ (visible) variables ----" << messaget::eom;
  for(std::map<edget,unsigned>::const_iterator it=map_from_e.begin();
    it!=map_from_e.end(); ++it)
    instrumenter.message.statistics() << it->first.first << ","
      << it->first.second << messaget::eom;
  instrumenter.message.statistics() << "---- cmp (invisible) variables ----"
    << messaget::eom;
  for(std::map<edget,unsigned>::const_iterator it=
    invisible_var.map_from_e.begin();
    it!=invisible_var.map_from_e.end(); ++it)
    instrumenter.message.statistics() << it->first.first << ","
      << it->first.second << messaget::eom;
  instrumenter.message.statistics() << "-----------------------------------"
    << messaget::eom;
}

/*******************************************************************\

Function: fence_insertert::get_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet fence_insertert::get_type(const irep_idt& id) {
  std::string copy=id2string(id);
  /* if we picked an array, removes [] that rw_set added */
  if(copy.find("[]")!=std::string::npos)
    copy=copy.substr(0, copy.find_last_of("[]")-1);
  try {
    return instrumenter.ns.lookup(copy).type;
  }
  catch (...) {
    std::list<std::string> fields;
    std::string current;

    /* collects the consecutive fields */
    std::string::const_iterator it=copy.begin();
    std::string::const_iterator next=it;
    for(; it!=copy.end(); ++it)
    {
      next=it;
      ++next;
      if(! (*it=='.' || (next!=copy.end() && *it=='-' && *next=='>')) ) {
        current+=*it;
        instrumenter.message.debug() << current << messaget::eom;
      }
      else {
        fields.push_back(current);
        current.clear();
        if(*it!='.')
          ++it;
        /* safe as next!=copy.end() */
        assert(next!=copy.end());
      }
    }

    /* retrieves the type of the accessed field */
    typet field=type_component(fields.begin(), fields.end(),
      instrumenter.ns.lookup(fields.front()).type);
    return field;
  }
}

/*******************************************************************\

Function: fence_insertert::type_component

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typet fence_insertert::type_component(std::list<std::string>::const_iterator it,
  std::list<std::string>::const_iterator end, const typet& type)
{
  if(it==end)
    return type;

  if(type.id()==ID_struct) {
    const struct_union_typet& str=to_struct_union_type(type);
    typet comp_type=str.component_type(*it);
    ++it;
    return type_component(it, end, comp_type);
  }

  if(type.id()==ID_symbol) {
    return type;
  }

  assert(0);
}

