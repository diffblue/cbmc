/*******************************************************************\

Module: data dependencies

Author: Vincent Nimal

Date: 2012

\*******************************************************************/

/// \file
/// data dependencies

#include "data_dp.h"

#include <util/invariant.h>
#include <util/message.h>

#include "abstract_event.h"

/// insertion
void data_dpt::dp_analysis(
  const datat &read,
  bool local_read,
  const datat &write,
  bool local_write)
{
  data_typet::const_iterator it;

  for(it=data.cbegin(); it!=data.cend(); ++it)
  {
    if(local_read && it->id==read.id)
    {
      data.insert(
        datat(
          write.id,
          (local_write?source_locationt():write.loc),
          it->eq_class));
      continue;
    }

    if(local_write && it->id==write.id)
    {
      data.insert(
        datat(
          read.id,
          (local_read?source_locationt():read.loc),
          it->eq_class));
      continue;
    }
  }

  if(it==data.cend())
  {
    ++class_nb;
    data.insert(
      datat(read.id, (local_read?source_locationt():read.loc), class_nb));
    data.insert(
      datat(write.id, (local_write?source_locationt():write.loc), class_nb));
  }
}

void data_dpt::dp_analysis(
  const abstract_eventt &read,
  const abstract_eventt &write)
{
  datat d_read(read.variable, read.source_location);
  datat d_write(write.variable, write.source_location);
  dp_analysis(d_read, read.local, d_write, write.local);
}

/// search in N^2
bool data_dpt::dp(const abstract_eventt &e1, const abstract_eventt &e2) const
{
  for(auto it1=data.cbegin(); it1!=data.cend(); ++it1)
  {
    auto it2=it1;
    ++it2;
    if(it2==data.cend())
      break;

    if(e1.local)
    {
      if(it1->id != e1.variable)
        continue;
    }
    else
    {
      if(it1->id!=e1.variable || it1->loc!=e1.source_location)
        continue;
    }

    for(; it2!=data.cend(); ++it2)
    {
      if(e2.local)
      {
        if(it2->id!=e2.variable)
          continue;
      }
      else
      {
        if(it2->id!=e2.variable || it2->loc!=e2.source_location)
          continue;
      }
      /* or else, same class */
      if(it1->eq_class==it2->eq_class)
      {
        // message.debug() << e1<<"-dp->"<<e2 << messaget::eom;
        return true;
      }
    }
  }
  // message.debug() << e1<<"-x->"<<e2 << messaget::eom;
  return false;
}

/// merge in N^3
void data_dpt::dp_merge()
{
  if(data.size()<2)
    return;

  unsigned initial_size=data.size();

  unsigned from=0;
  unsigned to=0;

  /* look for similar elements */
  for(auto it1=data.cbegin(); it1!=data.cend(); ++it1)
  {
    auto it2=it1;
    ++it2;
    /* all ok -- ends */
    if(it2==data.cend())
      return;

    for(; it2!=data.cend(); ++it2)
    {
      if(it1 == it2)
      {
        from=it2->eq_class;
        to=it1->eq_class;
        data.erase(it2);
        break;
      }
    }
  }

  /* merge */
  for(auto it3=data.begin(); it3!=data.end(); ++it3)
    if(it3->eq_class==from)
      it3->eq_class=to;

  /* strictly monotonous => converges */
  INVARIANT(initial_size>data.size(), "strictly monotonous => converges");

  /* repeat until classes are disjunct */
  dp_merge();
}

void data_dpt::print(messaget &message)
{
#ifdef DEBUG
  data_typet::const_iterator it;
  std::map<unsigned, std::set<source_locationt> > classed;

  for(it=data.cbegin(); it!=data.cend(); ++it)
  {
    if(classed.find(it->eq_class)==classed.end())
    {
      std::set<source_locationt> s;
      s.insert(it->loc);
      classed[it->eq_class]=s;
    }
    else
      classed[it->eq_class].insert(it->loc);
  }

  for(std::map<unsigned, std::set<source_locationt> >::const_iterator
      m_it=classed.begin();
      m_it!=classed.end(); ++m_it)
  {
    message.debug() << "class #"<<m_it->first << messaget::eom;
    std::set<source_locationt>::const_iterator l_it;
    for(l_it=m_it->second.begin(); l_it!=m_it->second.end(); ++l_it)
      message.debug()<< "loc: "<<*l_it << messaget::eom;
  }
#else
  (void)message; // unused parameter
#endif
}
