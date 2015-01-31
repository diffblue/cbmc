/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include "byte_operators.h"
#include "config.h"

/*******************************************************************\

Function: byte_extract_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt byte_extract_id()
{
  switch(config.ansi_c.endianness)
  {
  case configt::ansi_ct::IS_LITTLE_ENDIAN:
    return ID_byte_extract_little_endian;

  case configt::ansi_ct::IS_BIG_ENDIAN:
    return ID_byte_extract_big_endian;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: byte_update_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

irep_idt byte_update_id()
{
  switch(config.ansi_c.endianness)
  {
  case configt::ansi_ct::IS_LITTLE_ENDIAN:
    return ID_byte_update_little_endian;

  case configt::ansi_ct::IS_BIG_ENDIAN:
    return ID_byte_update_big_endian;

  default:
    assert(false);
  }
}
