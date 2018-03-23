/*******************************************************************\

Module: Hashing IREPs

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Hashing IREPs

#include "irep_hash_container.h"

#include "irep.h"
#include "irep_hash.h"

size_t irep_hash_container_baset::number(const irept &irep)
{
  // the ptr-hash provides a speedup of up to 3x

  ptr_hasht::const_iterator it=ptr_hash.find(&irep.read());

  if(it!=ptr_hash.end())
    return it->second.number;

  packedt packed;
  pack(irep, packed);
  size_t id=numbering.number(packed);

  auto &irep_entry = ptr_hash[&irep.read()];
  irep_entry.number = id;
  irep_entry.irep = irep;

  return id;
}

size_t irep_hash_container_baset::vector_hasht::operator()(
  const packedt &p) const
{
  size_t result=p.size(); // seed
  for(auto elem : p)
    result=hash_combine(result, elem);
  return result;
}

void irep_hash_container_baset::pack(
  const irept &irep,
  packedt &packed)
{
  const irept::subt &sub=irep.get_sub();
  const irept::named_subt &named_sub=irep.get_named_sub();
  const irept::named_subt &comments=irep.get_comments();

#ifdef SUB_IS_LIST
  const std::size_t named_sub_size =
    std::distance(named_sub.begin(), named_sub.end());
  const std::size_t comments_size = full ?
    std::distance(comments.begin(), comments.end()) : 0;
#else
  const std::size_t named_sub_size = named_sub.size();
  const std::size_t comments_size = full ? comments.size() : 0;
#endif
  packed.reserve(1 + 1 + sub.size() + named_sub_size * 2 + comments_size * 2);

  packed.push_back(irep_id_hash()(irep.id()));

  packed.push_back(sub.size());
  forall_irep(it, sub)
    packed.push_back(number(*it));

  packed.push_back(named_sub_size);
  forall_named_irep(it, named_sub)
  {
    packed.push_back(irep_id_hash()(it->first)); // id
    packed.push_back(number(it->second)); // sub-irep
  }

  if(full)
  {
    packed.push_back(comments_size);
    forall_named_irep(it, comments)
    {
      packed.push_back(irep_id_hash()(it->first)); // id
      packed.push_back(number(it->second)); // sub-irep
    }
  }
}
