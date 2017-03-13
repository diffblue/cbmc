/*******************************************************************\

Module: util

Author: Reuben Thomas, reuben.thomas@me.com

\*******************************************************************/

#ifndef CPROVER_UTIL_IREP_IDS_H
#define CPROVER_UTIL_IREP_IDS_H

#include "dstring.h"

enum class idt:unsigned
{
#define IREP_ID_ONE(the_id) id_##the_id,
#define IREP_ID_TWO(the_id, str) id_##the_id,

#include "irep_ids.def"
};

#ifdef USE_DSTRING

#define IREP_ID_ONE(the_id)                                                    \
  static const dstringt ID_##the_id=                                           \
    dstringt::make_from_table_index(static_cast<unsigned>(idt::id_##the_id));
#define IREP_ID_TWO(the_id, str)                                               \
  static const dstringt ID_##the_id=                                           \
    dstringt::make_from_table_index(static_cast<unsigned>(idt::id_##the_id));

#else

#define IREP_ID_ONE(the_id)                                                    \
  static const std::string ID_##the_id(#the_id);
#define IREP_ID_TWO(the_id, str)                                               \
  static const std::string ID_##the_id(#the_id);

#endif

#include "irep_ids.def" // NOLINT(build/include)

#endif
