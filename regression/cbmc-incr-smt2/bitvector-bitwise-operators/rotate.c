int main()
{
  unsigned a;
  __CPROVER_assume(a == 0x12345678u);

  // Rotate left by 8: 0x12345678 -> 0x34567812
  unsigned rl = __builtin_rotateleft32(a, 8);
  __CPROVER_assert(rl == 0x34567812u, "rotl32 by 8");

  // Rotate right by 8: 0x12345678 -> 0x78123456
  unsigned rr = __builtin_rotateright32(a, 8);
  __CPROVER_assert(rr == 0x78123456u, "rotr32 by 8");

  // Rotate by 0 is identity
  __CPROVER_assert(
    __builtin_rotateleft32(a, 0) == a, "rotl32 by 0 is identity");
}
