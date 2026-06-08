int main()
{
  // Item 13 / Bug A soundness regression.
  // (a*b)*c == a*(b*c) on 9-bit operands. C integer promotion
  // computes the assertion products at 32 bits, where the identity
  // does NOT hold (the 9-bit truncation of a*b loses bits that
  // matter at 32 bits). The algebraic pre-solver previously
  // reasoned in the 9-bit ring and wrongly proved this SUCCESSFUL.
  // Correct result (per bit-blasting and z3) is FAILED.
  __CPROVER_bitvector[9] a, b, c;
  __CPROVER_bitvector[9] ab = a * b, bc = b * c;
  __CPROVER_assert(ab * c == a * bc, "associativity (must be FAILED)");
}
