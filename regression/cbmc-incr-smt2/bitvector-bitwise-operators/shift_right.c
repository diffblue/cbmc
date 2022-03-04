#include <stdint.h>

// In C, whether a right-shift is arithmetic or logical depends on the
// original type being shifted. An unsigned value will be shifted to
// the right in a logical manner (this assigns `0` to the leftmost bit).
// If the type is signed, right shift will assign the sign bit to the
// leftmost digit.

int main()
{
  int first;
  uint8_t second;

  int place;
  __CPROVER_assume(place >= 1);

  int result_signed = first >> place;
  uint8_t result_unsigned = second >> place;

  // This assertion captures the intend of the expected behaviour of
  // bit-shifting an unsigned int (logical shift)
  __CPROVER_assert(
    result_unsigned != 64,
    "Right shifting a uint with leftmost bit set is a logical shift");
  // The following assertions capture the expected behaviour of
  // a right logical (in the case of a signed positive int) and
  // arithmetic shift (in the case of a signed negative int).
  if(first >= 0)
  {
    __CPROVER_assert(
      result_signed >= 0,
      "Right shifting a positive number has a lower bound of 0");
  }
  else
  {
    __CPROVER_assert(
      result_signed <= -1,
      "Right shifting a negative number has a lower bound value of -1");
  }
}
