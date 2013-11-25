/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_MERGE_IREP_H
#define CPROVER_MERGE_IREP_H

#include "irep.h"
#include "hash_cont.h"

// Warning: the below uses irep_hash, as opposed to irep_full_hash,
// i.e., any comments will be disregarded during merging. Use
// merge_full_irept if any comments are of importance.

class merge_irept
{
public:
  void operator()(irept &);

protected:
  typedef hash_set_cont<irept, irep_hash> irep_storet;
  irep_storet irep_store;     

  const irept& merged(const irept &irep);
};

class merge_full_irept
{
public:
  void operator()(irept &);

protected:
  typedef hash_set_cont<irept, irep_full_hash, irep_full_eq> irep_storet;
  irep_storet irep_store;     

  const irept& merged(const irept &irep);
};

#endif
