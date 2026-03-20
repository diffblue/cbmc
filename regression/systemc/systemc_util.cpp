#include "systemc_util.h"

void bitvector_assign_to(
  const bv_type &src,
  bv_type &dst,
  int offset,
  int length)
{
  //TODO: we have to expose the bitvector_extract operator at the interface
  bv_type tmpsrc = src;
  tmpsrc <<= MAX_SIZE-length;
  tmpsrc >>= MAX_SIZE-length;
  tmpsrc <<= offset;
  bv_type tmpdst1 = dst;
  // Shifts by offset+length or MAX_SIZE-offset may equal the bit width
  // when extracting a full-width or zero-offset slice. This is technically
  // undefined in C/C++ but intentionally used here to clear bits.
#pragma CPROVER check push
#pragma CPROVER check disable "undefined-shift"
  tmpdst1 >>= offset+length;
  tmpdst1 <<= offset+length;
  bv_type tmpdst2 = dst;
  tmpdst2 <<= MAX_SIZE-offset;
  tmpdst2 >>= MAX_SIZE-offset;
#pragma CPROVER check pop
  dst = tmpdst1 | tmpsrc | tmpdst2;
}

void bitvector_assign_from(
  const bv_type &src,
  int offset,
  int length,
  bv_type &dst)
{
  //TODO: we have to expose the bitvector_extract operator at the interface
  dst = src;
  dst <<= MAX_SIZE-(offset+length);
  dst >>= MAX_SIZE-length;
}
