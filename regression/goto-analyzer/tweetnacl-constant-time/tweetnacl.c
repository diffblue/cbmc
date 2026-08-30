/*
 * Simplified subset of TweetNaCl cryptographic library
 * For testing constant-time properties with CBMC's dependence graph analysis
 *
 * TweetNaCl claims to have no data-dependent branches or array indices.
 * This test verifies these claims using goto-analyzer --dependence-graph
 *
 * Reference: https://github.com/diffblue/cbmc/issues/366
 * Based on TweetNaCl: https://tweetnacl.cr.yp.to/
 * Public domain code
 */

typedef unsigned char u8;
typedef unsigned int u32;
typedef unsigned long long u64;

// Constant-time selection (sel25519 from TweetNaCl)
// Uses bitwise mask instead of if-statement: no branches at all
u64 sel25519(u64 a, u64 b, u64 c)
{
  u64 mask = ~(c - 1);
  return a ^ ((a ^ b) & mask);
}

// Constant-time byte comparison (crypto_verify_16 from TweetNaCl)
// Loop bound is constant 16, not dependent on secret data
int crypto_verify_16(const u8 *x, const u8 *y)
{
  u32 d = 0;
  int i;
  for(i = 0; i < 16; i++)
    d |= x[i] ^ y[i];
  return (1 & ((d - 1) >> 8)) - 1;
}

// Constant-time conditional swap (from Curve25519)
// Loop bound is constant 32, not dependent on secret swap bit b
void cswap(u64 p[32], u64 q[32], u8 b)
{
  int i;
  u64 mask = ~((u64)b - 1);
  for(i = 0; i < 32; i++)
  {
    u64 t = (p[i] ^ q[i]) & mask;
    p[i] ^= t;
    q[i] ^= t;
  }
}

int main(void)
{
  u8 secret_key[32];
  u8 msg1[16], msg2[16];
  u64 x[32], z[32];

  // Test constant-time selection
  u64 sel_result = sel25519(42, 99, secret_key[0] & 1);

  // Test constant-time comparison
  int verify_result = crypto_verify_16(msg1, msg2);

  // Test constant-time swap
  cswap(x, z, secret_key[1] & 1);

  return (sel_result + verify_result + x[0]) & 1;
}
