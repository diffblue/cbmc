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
  tmpdst1 >>= offset+length;
  tmpdst1 <<= offset+length;
  bv_type tmpdst2 = dst;
  tmpdst2 <<= MAX_SIZE-offset;
  tmpdst2 >>= MAX_SIZE-offset;
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
