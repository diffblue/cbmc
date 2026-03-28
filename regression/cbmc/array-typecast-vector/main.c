// Exercises the SMT2-incremental backend's array-to-array typecast
// encoding via a GCC vector_size cast: int32x4 -> int64x2 (widening).
// Without the fix in this PR, the incremental SMT2 backend bailed out
// on the array-to-array typecast in vector lowering.
//
// The lane convention (which int32 ends up where in each int64) follows
// the configured target endianness; with the cbmc default (little-endian
// x86_64), the lower-indexed source elements occupy the least
// significant bits of the corresponding target element.

typedef int v4si __attribute__((vector_size(16)));
typedef long long v2di __attribute__((vector_size(16)));

int main(void)
{
  v4si a = {0x11111111, 0x22222222, 0x33333333, 0x44444444};
  v2di b = (v2di)a;

  // On little-endian, a[0] (low source idx) goes to the LSBs of b[0] and
  // a[1] (next source idx) goes to the more significant 32 bits.
  __CPROVER_assert(
    b[0] == ((long long)0x22222222LL << 32 | 0x11111111LL),
    "lane 0 little-endian");
  __CPROVER_assert(
    b[1] == ((long long)0x44444444LL << 32 | 0x33333333LL),
    "lane 1 little-endian");

  return 0;
}
