/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// ANSI-C Language Conversion

#ifndef CPROVER_ANSI_C_ANSI_C_CONVERT_TYPE_H
#define CPROVER_ANSI_C_ANSI_C_CONVERT_TYPE_H

#include <util/std_expr.h>

#include "c_qualifiers.h"
#include "c_storage_spec.h"

#include <list>

class message_handlert;

class ansi_c_convert_typet
{
public:
  unsigned unsigned_cnt, signed_cnt, char_cnt,
           int_cnt, short_cnt, long_cnt,
           double_cnt, float_cnt, c_bool_cnt,
           proper_bool_cnt, complex_cnt;

  // extensions
  unsigned int8_cnt, int16_cnt, int32_cnt, int64_cnt,
           ptr32_cnt, ptr64_cnt,
           gcc_float16_cnt,
           gcc_float32_cnt, gcc_float32x_cnt,
           gcc_float64_cnt, gcc_float64x_cnt,
           gcc_float128_cnt, gcc_float128x_cnt,
           gcc_int128_cnt,
           bv_cnt,
           floatbv_cnt, fixedbv_cnt;

  typet gcc_attribute_mode;

  bool packed, aligned;
  exprt vector_size, alignment, bv_width, fraction_width;
  exprt msc_based; // this is Visual Studio
  bool constructor, destructor;

  // contracts
  exprt::operandst assigns, frees, ensures, requires;

  // storage spec
  c_storage_spect c_storage_spec;

  // qualifiers
  c_qualifierst c_qualifiers;

  virtual void write(typet &type);

  source_locationt source_location;

  std::list<typet> other;

  ansi_c_convert_typet(message_handlert &_message_handler, const typet &type)
    : ansi_c_convert_typet(_message_handler)
  {
    source_location = type.source_location();
    read_rec(type);
  }

protected:
  message_handlert &message_handler;

  // Default-initialize all members. To be used by classes deriving from this
  // one to make sure additional members can be initialized before invoking
  // read_rec.
  explicit ansi_c_convert_typet(message_handlert &_message_handler)
    : unsigned_cnt(0),
      signed_cnt(0),
      char_cnt(0),
      int_cnt(0),
      short_cnt(0),
      long_cnt(0),
      double_cnt(0),
      float_cnt(0),
      c_bool_cnt(0),
      proper_bool_cnt(0),
      complex_cnt(0),
      int8_cnt(0),
      int16_cnt(0),
      int32_cnt(0),
      int64_cnt(0),
      ptr32_cnt(0),
      ptr64_cnt(0),
      gcc_float16_cnt(0),
      gcc_float32_cnt(0),
      gcc_float32x_cnt(0),
      gcc_float64_cnt(0),
      gcc_float64x_cnt(0),
      gcc_float128_cnt(0),
      gcc_float128x_cnt(0),
      gcc_int128_cnt(0),
      bv_cnt(0),
      floatbv_cnt(0),
      fixedbv_cnt(0),
      gcc_attribute_mode(static_cast<const typet &>(get_nil_irep())),
      packed(false),
      aligned(false),
      vector_size(nil_exprt{}),
      alignment(nil_exprt{}),
      bv_width(nil_exprt{}),
      fraction_width(nil_exprt{}),
      msc_based(nil_exprt{}),
      constructor(false),
      destructor(false),
      message_handler(_message_handler)
  {
  }

  virtual void read_rec(const typet &type);
  virtual void build_type_with_subtype(typet &type) const;
  virtual void set_attributes(typet &type) const;
};

#endif // CPROVER_ANSI_C_ANSI_C_CONVERT_TYPE_H
