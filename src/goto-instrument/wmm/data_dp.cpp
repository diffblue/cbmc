/*******************************************************************\

Module: data dependencies

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

#include "data_dp.h"

#include "abstract_event.h"

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#include <map>
#define DEBUG_MESSAGE(a) std::cout<<a<<std::endl
#else
#define DEBUG_MESSAGE(a)
#endif

/*******************************************************************\

Function: data_dpt::dp_analysis

  Inputs:

 Outputs:

 Purpose: insertion

\*******************************************************************/

void data_dpt::dp_analysis(
  const datat& read, 
  bool local_read, 
  const datat& write, 
  bool local_write)
{
  const_iterator it;

  for(it=begin(); it!=end(); ++it)
  {
    if(local_read && it->id==read.id)
    {
      insert(datat(write.id, (local_write?locationt():write.loc), it->eq_class));
      continue;
    }

    if(local_write && it->id==write.id)
    {
      insert(datat(read.id, (local_read?locationt():read.loc), it->eq_class));
      continue;
    }
  }

  if(it==end())
  {
    ++class_nb;
    insert(datat(read.id, (local_read?locationt():read.loc), class_nb));
    insert(datat(write.id, (local_write?locationt():write.loc), class_nb));
  }
}

/*******************************************************************\

Function: data_dpt::dp_analysis

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_dpt::dp_analysis(const abstract_eventt& read, 
  const abstract_eventt& write)
{
  datat d_read(read.variable,read.location);
  datat d_write(write.variable,write.location);
  dp_analysis(d_read,read.local,d_write,write.local);
}

/*******************************************************************\

Function: data_dpt::dp

  Inputs:

 Outputs:

 Purpose: search in N^2

\*******************************************************************/

bool data_dpt::dp(const abstract_eventt& e1, const abstract_eventt& e2) const
{
  for(const_iterator it1=begin(); it1!=end(); ++it1)
  {
    const_iterator it2=it1;
    ++it2;
    if(it2==end())
      break;

    if(e1.local)
    {
      if(it1->id != e1.variable)
        continue;
    }
    else
    {
      if(it1->id!=e1.variable || it1->loc!=e1.location)
        continue;
    }

    for(; it2!=end(); ++it2)
    {
      if(e2.local)
      {
        if(it2->id!=e2.variable)
          continue;
      }
      else
      {
        if(it2->id!=e2.variable || it2->loc!=e2.location)
          continue;
      }
      /* or else, same class */
      if(it1->eq_class==it2->eq_class)
      {
        DEBUG_MESSAGE(e1<<"-dp->"<<e2);
        return true;
      }
    }
  }
  DEBUG_MESSAGE(e1<<"-x->"<<e2);
  return false;
}

/*******************************************************************\

Function: data_dpt::dp_merge

  Inputs:

 Outputs:

 Purpose:  merge in N^3

\*******************************************************************/

void data_dpt::dp_merge()
{
  if(size()<2)
    return;

  unsigned initial_size=size();

  unsigned from=0;
  unsigned to=0;

  /* look for similar elements */
  for(const_iterator it1=begin(); it1!=end(); ++it1)
  {
    const_iterator it2=it1;
    ++it2;
    /* all ok -- ends */
    if(it2==end())
      return;

    for(; it2!=end(); ++it2)
    {
      if(it1 == it2)
      {
        from=it2->eq_class;
        to=it1->eq_class;
        erase(it2);
        break;
      }
    }
  }

  /* merge */
  for(iterator it3=begin(); it3!=end(); ++it3)
    if(it3->eq_class==from)
      it3->eq_class=to;

  /* strictly monotonous => converges */
  assert(initial_size>size());

  /* repeat until classes are disjunct */
  dp_merge();
}

/*******************************************************************\

Function: data_dpt::print

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void data_dpt::print()
{
#ifdef DEBUG
  const_iterator it;
  std::map<unsigned,std::set<locationt> > classed;

  for(it=begin(); it!=end(); ++it)
  {
    if(classed.find(it->eq_class)==classed.end())
    {
      std::set<locationt> s;
      s.insert(it->loc);
      classed[it->eq_class]=s;
    }
    else
      classed[it->eq_class].insert(it->loc);
  }

  for(std::map<unsigned,std::set<locationt> >::const_iterator m_it=classed.begin();
    m_it!=classed.end(); ++m_it)
  {
    DEBUG_MESSAGE("class #"<<m_it->first);
    std::set<locationt>::const_iterator l_it;
    for(l_it=m_it->second.begin(); l_it!=m_it->second.end(); ++l_it)
      DEBUG_MESSAGE("loc: "<<*l_it);
  }
#endif
}

