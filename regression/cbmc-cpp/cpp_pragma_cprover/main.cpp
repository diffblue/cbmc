// Test that #pragma CPROVER check works in C++ mode
int main()
{
  unsigned x = 1;
#pragma CPROVER check push
#pragma CPROVER check disable "undefined-shift"
  // This shift should NOT generate a check
  unsigned y = x << 32;
#pragma CPROVER check pop
  // This shift SHOULD generate a check
  unsigned z = x << 32;
}
