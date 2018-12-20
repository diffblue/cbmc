/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "byte_operators.h"

#include "config.h"

irep_idt byte_extract_id()
{
  switch(config.ansi_c.endianness)
  {
  case configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN:
    return ID_byte_extract_little_endian;

  case configt::ansi_ct::endiannesst::IS_BIG_ENDIAN:
    return ID_byte_extract_big_endian;

  default:
    UNREACHABLE;
  }

  UNREACHABLE;
}

irep_idt byte_update_id()
{
  switch(config.ansi_c.endianness)
  {
  case configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN:
    return ID_byte_update_little_endian;

  case configt::ansi_ct::endiannesst::IS_BIG_ENDIAN:
    return ID_byte_update_big_endian;

  default:
    UNREACHABLE;
  }

  UNREACHABLE;
}
