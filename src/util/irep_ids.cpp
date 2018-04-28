/*******************************************************************\

Module: Internal Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Internal Representation

#include "irep_ids.h"

#include "invariant.h"

#include "string_container.h"

const char *irep_ids_table[]=
{
#define IREP_ID_ONE(id) #id,
#define IREP_ID_TWO(id, str) #str,

#include "irep_ids.def"

  nullptr,
};

#ifdef USE_DSTRING

#else

#define IREP_ID_ONE(the_id) const std::string ID_##the_id(#the_id);
#define IREP_ID_TWO(the_id, str) const std::string ID_##the_id(#the_id);

#include "irep_ids.def" // NOLINT(build/include)

#endif

string_containert::string_containert()
{
  // pre-allocate empty string -- this gets index 0
  get("");

  // allocate strings
  for(unsigned i=0; irep_ids_table[i]!=nullptr; i++)
  {
    unsigned x=operator[](irep_ids_table[i]);
    INVARIANT(x==i, "i-th element is inserted at position i"); // sanity check
  }
}
