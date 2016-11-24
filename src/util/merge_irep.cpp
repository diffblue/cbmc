/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "irep_hash.h"
#include "merge_irep.h"

/*******************************************************************\

Function: to_be_merged_irept::hash

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::size_t to_be_merged_irept::hash() const
{
  std::size_t result=hash_string(id());

  const irept::subt &sub=get_sub();
  const irept::named_subt &named_sub=get_named_sub();
  
  forall_irep(it, sub)
    result=hash_combine(result, static_cast<const merged_irept &>(*it).hash());

  forall_named_irep(it, named_sub)
  {
    result=hash_combine(result, hash_string(it->first));
    result=hash_combine(result, static_cast<const merged_irept &>(it->second).hash());
  }

  result=hash_finalize(result, named_sub.size()+sub.size());

  return result;
}

/*******************************************************************\

Function: to_be_merged_irept::operator==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool to_be_merged_irept::operator == (const to_be_merged_irept &other) const
{
  if(id()!=other.id()) return false;

  const irept::subt &sub=get_sub();
  const irept::subt &o_sub=other.get_sub();
  const irept::named_subt &named_sub=get_named_sub();
  const irept::named_subt &o_named_sub=other.get_named_sub();

  if(sub.size()!=o_sub.size()) return true;
  if(named_sub.size()!=o_named_sub.size()) return true;

  {
    irept::subt::const_iterator s_it=sub.begin();
    irept::subt::const_iterator os_it=o_sub.begin();
  
    for(; s_it!=sub.end(); s_it++, os_it++)
      if(static_cast<const merged_irept &>(*s_it)!=
         static_cast<const merged_irept &>(*os_it))
        return false;
  }
  
  {
    irept::named_subt::const_iterator s_it=named_sub.begin();
    irept::named_subt::const_iterator os_it=o_named_sub.begin();
  
    for(; s_it!=named_sub.end(); s_it++, os_it++)
      if(s_it->first!=os_it->first ||
         static_cast<const merged_irept &>(s_it->second)!=
         static_cast<const merged_irept &>(os_it->second))
        return false;
  }

  return true;
}

/*******************************************************************\

Function: merged_irepst::merged

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const merged_irept &merged_irepst::merged(const irept &irep)
{
  // first see if it's already a merged_irep

  merged_irep_storet::const_iterator entry=
    merged_irep_store.find(merged_irept(irep));

  if(entry!=merged_irep_store.end())
    return *entry; // nothing to do

  // need to build new irep that will be in the container
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

  std::pair<to_be_merged_irep_storet::const_iterator, bool> result=
    to_be_merged_irep_store.insert(to_be_merged_irept(new_irep));

  if(result.second) // really new, record
    merged_irep_store.insert(merged_irept(new_irep));
  
  return static_cast<const merged_irept &>(static_cast<const irept &>(*result.first));
}

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
