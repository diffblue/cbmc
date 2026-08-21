// If-conversion linearises side-effect-free conditional assignments so that
// --paths mode does not fork at them. The 16 independent conditional
// assignments below would create 2^16 = 65536 symbolic-execution paths
// without the transformation (timing out under the harness limit); with it
// they become 16 branch-free guarded assignments and a single path remains.
// Reverting the pass is therefore observable here as a timeout.

int main(void)
{
  unsigned int cond; // nondeterministic
  int g = 0;

  if(cond & (1u << 0))
    g = 1;
  if(cond & (1u << 1))
    g = 2;
  if(cond & (1u << 2))
    g = 3;
  if(cond & (1u << 3))
    g = 4;
  if(cond & (1u << 4))
    g = 5;
  if(cond & (1u << 5))
    g = 6;
  if(cond & (1u << 6))
    g = 7;
  if(cond & (1u << 7))
    g = 8;
  if(cond & (1u << 8))
    g = 9;
  if(cond & (1u << 9))
    g = 10;
  if(cond & (1u << 10))
    g = 11;
  if(cond & (1u << 11))
    g = 12;
  if(cond & (1u << 12))
    g = 13;
  if(cond & (1u << 13))
    g = 14;
  if(cond & (1u << 14))
    g = 15;
  if(cond & (1u << 15))
    g = 16;

  __CPROVER_assert(g >= 0 && g <= 16, "g stays within bounds");

  return 0;
}
