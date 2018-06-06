#include <cassert>
#include <stdint.h>
#include <stdbool.h>

#undef HOTFIX

typedef struct {
  uint32_t value_31_0 : 32;
} signal32_t;

typedef struct {
  uint8_t value_0_0 : 1;
} signal1_t;

static inline bool yosys_simplec_get_bit_25_of_32(const signal32_t *sig)
{
  return (sig->value_31_0 >> 25) & 1;
}

struct rvfi_insn_srai_state_t
{
  signal32_t rvfi_insn;
  signal32_t rvfi_rs1_rdata;
  signal1_t _abc_1398_n364;
  signal1_t _abc_1398_n363;
};

void test(rvfi_insn_srai_state_t state, bool valid)
{
#ifndef HOTFIX
  state._abc_1398_n364.value_0_0 = yosys_simplec_get_bit_25_of_32(&state.rvfi_insn) ?
      yosys_simplec_get_bit_25_of_32(&state.rvfi_rs1_rdata) : state._abc_1398_n363.value_0_0;
#else
  state._abc_1398_n364.value_0_0 = yosys_simplec_get_bit_25_of_32(&state.rvfi_insn) ?
      yosys_simplec_get_bit_25_of_32(&state.rvfi_rs1_rdata) : (bool)state._abc_1398_n363.value_0_0;
#endif

  assert(valid);
}

int main(int argc, char* argv[])
{
	rvfi_insn_srai_state_t state;
  bool valid;
  test(state, valid);
  return 0;
}
