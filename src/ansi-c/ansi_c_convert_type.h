/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_CONVERT_TYPE_H
#define CPROVER_ANSI_C_CONVERT_TYPE_H

#include <util/message_stream.h>

#include "c_types.h"
#include "c_qualifiers.h"
#include "c_storage_spec.h"

class ansi_c_convert_typet:public message_streamt
{
public:
  unsigned unsigned_cnt, signed_cnt, char_cnt,
           int_cnt, short_cnt, long_cnt,
           double_cnt, float_cnt, c_bool_cnt,
           proper_bool_cnt, complex_cnt;
  
  // extensions
  unsigned int8_cnt, int16_cnt, int32_cnt, int64_cnt,
           ptr32_cnt, ptr64_cnt,
           gcc_float128_cnt, gcc_int128_cnt, bv_cnt,
           floatbv_cnt, fixedbv_cnt;

  typet gcc_attribute_mode;
           
  bool packed, aligned;
  exprt vector_size, alignment, bv_width, fraction_width;
  exprt msc_based; // this is Visual Studio

  // storage spec
  c_storage_spect c_storage_spec;
       
  // qualifiers
  c_qualifierst c_qualifiers;

  void read(const typet &type);
  void write(typet &type);
  
  source_locationt source_location;
  
  std::list<typet> other;
  
  ansi_c_convert_typet(message_handlert &_message_handler):
    message_streamt(_message_handler)
  {
  }
  
  void clear()
  {
    unsigned_cnt=signed_cnt=char_cnt=int_cnt=short_cnt=
    long_cnt=double_cnt=float_cnt=c_bool_cnt=proper_bool_cnt=complex_cnt=
    int8_cnt=int16_cnt=int32_cnt=int64_cnt=
    ptr32_cnt=ptr64_cnt=
    gcc_float128_cnt=gcc_int128_cnt=bv_cnt=floatbv_cnt=fixedbv_cnt=0;
    vector_size.make_nil();
    alignment.make_nil();
    bv_width.make_nil();
    fraction_width.make_nil();
    msc_based.make_nil();
    gcc_attribute_mode.make_nil();
    
    packed=aligned=false;

    other.clear();
    c_storage_spec.clear();
    c_qualifiers.clear();
  }
  
protected:
  void read_rec(const typet &type);
};

#endif
