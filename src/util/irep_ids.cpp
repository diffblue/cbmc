/*******************************************************************\

Module: Internal Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Internal Representation

#include <cassert>

#include "irep_ids.h"
#include "string_container.h"

const char *irep_ids_table[]=
{
#define IREP_ID_ONE(id) #id,
#define IREP_ID_TWO(id, str) #str,

#include "irep_ids.def"

  nullptr,
};

#ifdef USE_DSTRING

#define IREP_ID_ONE(the_id)                                                    \
  const dstringt ID_##the_id=dstringt::make_from_table_index(                  \
      static_cast<unsigned>(idt::id_##the_id));
#define IREP_ID_TWO(the_id, str)                                               \
  const dstringt ID_##the_id=dstringt::make_from_table_index(                  \
      static_cast<unsigned>(idt::id_##the_id));

#else

#define IREP_ID_ONE(the_id) const std::string ID_##the_id(#the_id);
#define IREP_ID_TWO(the_id, str) const std::string ID_##the_id(#the_id);

#endif

#include "irep_ids.def" // NOLINT(build/include)

void initialize_string_container()
{
  // this is called by the constructor of string_containert

  for(unsigned i=0; irep_ids_table[i]!=nullptr; i++)
  {
    unsigned x;
    x=string_container[irep_ids_table[i]];
    assert(x==i); // sanity check
  }
}
