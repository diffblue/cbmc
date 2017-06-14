/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_MEMORY_MODELS_MM2CPP_H
#define CPROVER_MEMORY_MODELS_MM2CPP_H

#include <util/irep.h>

void mm2cpp(
  const irep_idt &,
  const irept &,
  std::ostream &);

#endif // CPROVER_MEMORY_MODELS_MM2CPP_H
