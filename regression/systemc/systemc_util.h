#ifndef SYSTEMC_UTIL_H
#define SYSTEMC_UTIL_H

//#define USE_BV

#ifdef USE_BV
#define MAX_SIZE 512
typedef __CPROVER::unsignedbv<MAX_SIZE> bv_type;
#else
typedef unsigned long bv_type;
#define MAX_SIZE (8*sizeof(bv_type))
#endif

void bitvector_assign_to(
  const bv_type &src,
  bv_type &dst,
  int offset,
  int length);

void bitvector_assign_from(
  const bv_type &src,
  int offset,
  int length,
  bv_type &dst);

#endif
