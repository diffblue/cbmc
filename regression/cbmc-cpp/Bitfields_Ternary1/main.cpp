#include <cassert>
#include <stdint.h>

// Regression test for issue where CBMC incorrectly failed with an
// "equality without matching types" error when using ternary expressions
// with bitfield types. The issue occurred when the third argument of a
// ternary operator was a bitfield type (uint8_t : 1) that needed to be
// implicitly converted to bool. GCC and Clang accept this code without
// warnings, and CBMC should handle the implicit conversion as well.

typedef struct
{
  uint32_t value_31_0 : 32;
} signal32_t;

typedef struct
{
  uint8_t value_0_0 : 1;
} signal1_t;

static inline bool yosys_simplec_get_bit_25_of_32(const signal32_t *sig)
{
  return (sig->value_31_0 >> 25) & 1;
}

typedef struct rvfi_insn_srai_state_t
{
  signal32_t rvfi_insn;
  signal32_t rvfi_rs1_rdata;
  signal1_t _abc_1398_n364;
  signal1_t _abc_1398_n363;
} rvfi_insn_srai_state_t;

int main()
{
  rvfi_insn_srai_state_t state;

  // Test case 1: op1 is bool (function-call result), op2 is a 1-bit
  // bit-field. Without the fix, typecheck_expr_trinary leaves op1 and
  // op2 with mismatched types after implicit conversion.
  state.rvfi_insn.value_31_0 = 0;
  state.rvfi_rs1_rdata.value_31_0 = 0;
  state._abc_1398_n363.value_0_0 = 1;

  // This ternary should work: condition ? bool : uint8_t:1
  // The third operand is a bitfield that should be implicitly converted to bool
  state._abc_1398_n364.value_0_0 =
    yosys_simplec_get_bit_25_of_32(&state.rvfi_insn)
      ? yosys_simplec_get_bit_25_of_32(&state.rvfi_rs1_rdata)
      : state._abc_1398_n363.value_0_0;

  // Since bit 25 of rvfi_insn is 0, the condition is false,
  // so the result should be _abc_1398_n363.value_0_0, which is 1
  assert(state._abc_1398_n364.value_0_0 == 1);

  // Test case 2: same operand shapes as test case 1 (op1 is bool from a
  // function call, op2 is the bit-field access state._abc_1398_n363.
  // value_0_0); only the condition is now true.
  state.rvfi_insn.value_31_0 = (1u << 25); // Set bit 25
  state.rvfi_rs1_rdata.value_31_0 = 0;

  state._abc_1398_n364.value_0_0 =
    yosys_simplec_get_bit_25_of_32(&state.rvfi_insn)
      ? yosys_simplec_get_bit_25_of_32(&state.rvfi_rs1_rdata)
      : state._abc_1398_n363.value_0_0;

  // Since bit 25 of rvfi_insn is 1, the condition is true,
  // so the result should be the bit 25 of rvfi_rs1_rdata, which is 0
  assert(state._abc_1398_n364.value_0_0 == 0);

  return 0;
}
