/*******************************************************************\

Module: Hashing IREPs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "irep_hash_container.h"
#include "irep.h"

/*******************************************************************\

Function: irep_hash_container_baset::number

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned irep_hash_container_baset::number(const irept &irep)
{ 
  // the ptr-hash provides a speedup of up to 3x
  
  ptr_hasht::const_iterator it=ptr_hash.find(&irep.read());
  
  if(it!=ptr_hash.end())
    return it->second;

  packedt packed;
  pack(irep, packed);
  unsigned id=numbering.number(packed);
  
  ptr_hash[&irep.read()]=id;
  
  return id;
}

/*******************************************************************\

Function: irep_hash_container_baset::pack

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void irep_hash_container_baset::pack(
  const irept &irep,
  packedt &packed)
{
  const irept::subt &sub=irep.get_sub();
  const irept::named_subt &named_sub=irep.get_named_sub();
  const irept::named_subt &comments=irep.get_comments();

  packed.reserve(
    1+1+sub.size()+named_sub.size()*2+
    full?comments.size()*2:0);
  
  packed.push_back(irep.id().get_no());

  packed.push_back(sub.size());  
  forall_irep(it, sub)
    packed.push_back(number(*it));

  packed.push_back(named_sub.size());
  forall_named_irep(it, named_sub)
  {
    packed.push_back(it->first.get_no()); // id
    packed.push_back(number(it->second)); // sub-irep
  }

  if(full)
  {
    packed.push_back(comments.size());
    forall_named_irep(it, comments)
    {
      packed.push_back(it->first.get_no()); // id
      packed.push_back(number(it->second)); // sub-irep
    }
  }
}

