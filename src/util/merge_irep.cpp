/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "merge_irep.h"

/*******************************************************************\

Function: merge_irept::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void merge_irept::operator()(irept &irep)
{
  // only useful if there is sharing
  #ifdef SHARING
  irep=merged(irep);
  #endif
}

/*******************************************************************\

Function: merge_irept::merged

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irept& merge_irept::merged(const irept &irep)
{
  irep_storet::const_iterator entry=irep_store.find(irep);
  if(entry!=irep_store.end())
    return *entry;

  irept new_irep(irep.id());

  const irept::subt &src_sub=irep.get_sub();
  irept::subt &dest_sub=new_irep.get_sub();
  dest_sub.reserve(src_sub.size());

  forall_irep(it, src_sub)
    dest_sub.push_back(merged(*it)); // recursive call

  const irept::named_subt &src_named_sub=irep.get_named_sub();
  irept::named_subt &dest_named_sub=new_irep.get_named_sub();

  forall_named_irep(it, src_named_sub)
    #ifdef SUB_IS_LIST
    dest_named_sub.push_back(
      std::make_pair(it->first, merged(it->second))); // recursive call
    #else
    dest_named_sub[it->first]=merged(it->second); // recursive call
    #endif

  return *irep_store.insert(new_irep).first;
}

/*******************************************************************\

Function: merge_full_irept::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void merge_full_irept::operator()(irept &irep)
{
  // only useful if there is sharing
  #ifdef SHARING
  irep=merged(irep);
  #endif
}

/*******************************************************************\

Function: merge_full_irept::merged

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const irept& merge_full_irept::merged(const irept &irep)
{
  irep_storet::const_iterator entry=irep_store.find(irep);
  if(entry!=irep_store.end())
    return *entry;

  irept new_irep(irep.id());

  const irept::subt &src_sub=irep.get_sub();
  irept::subt &dest_sub=new_irep.get_sub();
  dest_sub.reserve(src_sub.size());

  forall_irep(it, src_sub)
    dest_sub.push_back(merged(*it)); // recursive call

  const irept::named_subt &src_named_sub=irep.get_named_sub();
  irept::named_subt &dest_named_sub=new_irep.get_named_sub();

  forall_named_irep(it, src_named_sub)
    #ifdef SUB_IS_LIST
    dest_named_sub.push_back(
      std::make_pair(it->first, merged(it->second))); // recursive call
    #else
    dest_named_sub[it->first]=merged(it->second); // recursive call
    #endif

  const irept::named_subt &src_comments=irep.get_comments();
  irept::named_subt &dest_comments=new_irep.get_comments();

  forall_named_irep(it, src_comments)
    #ifdef SUB_IS_LIST
    dest_comments.push_back(
      std::make_pair(it->first, merged(it->second))); // recursive call
    #else
    dest_comments[it->first]=merged(it->second); // recursive call
    #endif

  return *irep_store.insert(new_irep).first;
}
