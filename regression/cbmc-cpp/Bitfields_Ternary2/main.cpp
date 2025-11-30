#include <cassert>
#include <stdint.h>

// Regression test that exercises the symmetric branch of
// cpp_typecheckt::typecheck_expr_trinary, where
//   implicit_conversion_sequence(op1, op2.type())
// fails but
//   implicit_conversion_sequence(op2, op1.type())
// succeeds. To trigger this we need an asymmetric conversion: the
// class types below have user-defined conversion operators, but the
// reverse direction is not available, so the first
// implicit_conversion_sequence call fails and the second one fires.
//
// Bitfields_Ternary1 covers the first branch; this test covers the
// second. The second test case below additionally pairs the
// user-defined conversion with a bit-field operand, which forces the
// new typecast fix-up inside the symmetric branch to fire (the
// implicit_conversion_sequence call strips the c_bit_field wrapper
// from the requested type, so the operand types still need to be
// re-aligned to the result type).

typedef struct
{
  uint8_t value_0_0 : 1;
} signal1_t;

// One-way conversion: class -> bool. There is no bool -> class_to_bool
// constructor, so implicit_conversion_sequence(bool, class) fails.
class class_to_bool
{
public:
  signal1_t s;
  operator bool() const
  {
    return s.value_0_0 != 0;
  }
};

// One-way conversion: class -> uint8_t. Used to pair against a
// bit-field operand on op1; the second-branch fix-up has to typecast
// op1 from c_bit_field<uint8_t,1> to uint8_t.
class class_to_uint8
{
public:
  uint8_t v;
  operator uint8_t() const
  {
    return v;
  }
};

int main()
{
  // Case 1: outer symmetric branch fires; types already align so the
  // inner if is skipped.
  {
    bool cond;
    class_to_bool holder;
    holder.s.value_0_0 = 1;

    // op1 is a bool literal, op2 is class_to_bool. First branch's
    // implicit_conversion_sequence(bool -> class_to_bool) fails (no
    // matching conversion); the symmetric branch then tries
    // implicit_conversion_sequence(class_to_bool -> bool), which
    // succeeds via operator bool(). The result type is bool.
    bool result = cond ? false : holder;

    // When cond is false we take op2 (class_to_bool -> bool == true
    // since value_0_0 == 1).
    if(!cond)
      assert(result == true);

    // When cond is true we take op1 (false).
    if(cond)
      assert(result == false);
  }

  // Case 2: outer symmetric branch fires AND the inner typecast
  // fix-up fires. op1 is a bit-field, op2 is class_to_uint8. The
  // first branch's implicit_conversion_sequence(bit-field ->
  // class_to_uint8) fails. The symmetric branch then converts op2 to
  // op1's bit-field type via operator uint8_t() + bit-field
  // promotion. The result type after the strip is plain uint8_t, but
  // op1 still wears the c_bit_field<uint8_t,1> label, so the new
  // fix-up must align it.
  {
    bool cond;
    signal1_t bf;
    bf.value_0_0 = 1;
    class_to_uint8 holder;
    holder.v = 7;

    uint8_t result = cond ? bf.value_0_0 : holder;

    if(!cond)
      assert(result == 7);

    if(cond)
      assert(result == 1);
  }

  return 0;
}
