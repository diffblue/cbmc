/*******************************************************************\

Module: ANSI-C Language Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_ANSI_C_CONVERT_TYPE_H
#define CPROVER_ANSI_C_CONVERT_TYPE_H

#include <message_stream.h>

#include <ansi-c/c_types.h>
#include <ansi-c/c_qualifiers.h>
#include <ansi-c/c_storage_spec.h>

class ansi_c_convert_typet:public message_streamt
{
public:
  unsigned unsigned_cnt, signed_cnt, char_cnt,
           int_cnt, short_cnt, long_cnt,
           double_cnt, float_cnt, bool_cnt,
           complex_cnt;
  
  // extensions
  unsigned int8_cnt, int16_cnt, int32_cnt, int64_cnt,
           ptr32_cnt, ptr64_cnt,
           gcc_float128_cnt, bv_cnt, bv_width;
  bool gcc_mode_QI, gcc_mode_HI, gcc_mode_SI, gcc_mode_DI;
           
  bool transparent_union, packed, aligned;
  exprt vector_size, alignment;

  // storage spec
  c_storage_spect c_storage_spec;
       
  // qualifiers
  c_qualifierst c_qualifiers;

  void read(const typet &type);
  void write(typet &type);
  
  locationt location;
  
  std::list<typet> other;
  
  ansi_c_convert_typet(message_handlert &_message_handler):
    message_streamt(_message_handler)
  {
  }
  
  void clear()
  {
    unsigned_cnt=signed_cnt=char_cnt=int_cnt=short_cnt=
    long_cnt=double_cnt=float_cnt=bool_cnt=complex_cnt=
    int8_cnt=int16_cnt=int32_cnt=int64_cnt=
    ptr32_cnt=ptr64_cnt=
    gcc_float128_cnt=bv_cnt=0;
    vector_size.make_nil();
    alignment.make_nil();
    bv_width=0;
    gcc_mode_QI=gcc_mode_HI=gcc_mode_SI=gcc_mode_DI=false;
    
    packed=aligned=transparent_union=false;

    other.clear();
    c_storage_spec.clear();
    c_qualifiers.clear();
  }
  
protected:
  void read_rec(const typet &type);
};

#endif
