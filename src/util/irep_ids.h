/*******************************************************************\

Module: util

Author: Reuben Thomas, reuben.thomas@me.com

\*******************************************************************/

/// \file
/// util

#ifndef CPROVER_UTIL_IREP_IDS_H
#define CPROVER_UTIL_IREP_IDS_H

#include "dstring.h"

/// \file
/// The irep_ids are generated using a technique called
/// [X-macros](https://en.wikipedia.org/wiki/X_Macro).
/// The ids are defined in the file irep_ids.def, using a pair of macros
/// `IREP_ID_ONE` and `IREP_ID_TWO`.
/// Definitions of the form `IREP_ID_ONE(param)` will be converted into a
/// const extern irep_idt with the variable name `ID_param` and the string
/// value `"param"`.
/// Definitions of the form `IREP_ID_TWO(param, contents)` will be converted
/// into a const extern irep_idt with the variable name `ID_param` and the
/// string value `"contents"`.

#define IREP_ID_ONE(the_id) extern const dstringt ID_##the_id;
#define IREP_ID_TWO(the_id, str) extern const dstringt ID_##the_id;

#include "irep_ids.def"

#endif
