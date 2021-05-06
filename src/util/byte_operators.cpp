/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "byte_operators.h"

#include "config.h"

static irep_idt byte_extract_id()
{
  switch(config.ansi_c.endianness)
  {
  case configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN:
    return ID_byte_extract_little_endian;

  case configt::ansi_ct::endiannesst::IS_BIG_ENDIAN:
    return ID_byte_extract_big_endian;

  case configt::ansi_ct::endiannesst::NO_ENDIANNESS:
    UNREACHABLE;
  }

  UNREACHABLE;
}

static irep_idt byte_update_id()
{
  switch(config.ansi_c.endianness)
  {
  case configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN:
    return ID_byte_update_little_endian;

  case configt::ansi_ct::endiannesst::IS_BIG_ENDIAN:
    return ID_byte_update_big_endian;

  case configt::ansi_ct::endiannesst::NO_ENDIANNESS:
    UNREACHABLE;
  }

  UNREACHABLE;
}

byte_extract_exprt
make_byte_extract(const exprt &_op, const exprt &_offset, const typet &_type)
{
  return byte_extract_exprt{byte_extract_id(), _op, _offset, _type};
}

byte_update_exprt
make_byte_update(const exprt &_op, const exprt &_offset, const exprt &_value)
{
  return byte_update_exprt{byte_update_id(), _op, _offset, _value};
}
