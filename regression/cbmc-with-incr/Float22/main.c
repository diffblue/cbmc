/*
** float-union-assignment.cpp
**
** Martin Brain
** martin.brain@cs.ox.ac.uk
** 26/09/12
**
** A reduced test case for problems with returning and assigning fields in a union.
**
*/

#include <assert.h>
#include <stdint.h>

typedef struct _components {
  unsigned int negative:1;
  unsigned int exponent:8;
  unsigned int mantissa:23;
} components;

typedef union _ieee754_float {
  components ieee;
  float f;
} ieee754_float;


float returnsField (uint32_t index) {
    ieee754_float c;

    c.ieee.negative = index & 0x1;
    c.ieee.exponent = 0;
    c.ieee.mantissa = 0;

    return c.f;
}

ieee754_float returnsStructure (uint32_t index) {
    ieee754_float c;

    c.ieee.negative = index & 0x1;
    c.ieee.exponent = 0;
    c.ieee.mantissa = 0;

    return c;
}


void testOne (void) {
   ieee754_float f1, f2;

   f1 = returnsStructure(0);
   f2 = returnsStructure(1);

   assert(f1.ieee.negative != f2.ieee.negative);

   return;
}


void testTwo (void) {
   ieee754_float f1, f2;

   f1 = returnsStructure(0);
   f2 = returnsStructure(1);

   assert(f1.ieee.negative != f2.ieee.negative);

   f1.f = returnsField(0);
   f2.f = returnsField(1);

   assert(f1.ieee.negative != f2.ieee.negative);

   return 1;
}


int testThree (void) {
   ieee754_float f1, f2;

   f1.f = returnsField(0);
   f2.f = returnsField(1);

   assert(f1.ieee.negative != f2.ieee.negative);

   return 1;
}

int main (void) {
  testOne();
  testTwo();
  testThree();

  return 0;
}
