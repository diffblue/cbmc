// AArch32 inline assembly (A32 code) that is interpreted exactly. The expected
// values were observed with an emulator.

// arm ldrex/orr/strex set a bit (atomic set)
void asm_case_0(unsigned long long *io)
{
  unsigned int m = (unsigned int)io[0];
  unsigned int v = (unsigned int)io[1];
  unsigned int tmp = (unsigned int)io[2];
  unsigned int res = (unsigned int)io[3];
  __asm__ __volatile__(
    "1: ldrex %0, [%2]\n"
    "   orr   %0, %0, %3\n"
    "   strex %1, %0, [%2]\n"
    "   teq   %1, #0\n"
    "   bne   1b\n"
    : "=&r"(tmp), "=&r"(res)
    : "r"(&m), "r"(v)
    : "cc", "memory");
  io[0] = (unsigned long long)m;
  io[1] = (unsigned long long)v;
  io[2] = (unsigned long long)tmp;
  io[3] = (unsigned long long)res;
}

// arm add and subtract
void asm_case_1(unsigned long long *io)
{
  unsigned int r = (unsigned int)io[0];
  unsigned int a = (unsigned int)io[1];
  unsigned int b = (unsigned int)io[2];
  unsigned int c = (unsigned int)io[3];
  __asm__("add %0, %1, %2\n sub %0, %0, %3"
          : "=&r"(r)
          : "r"(a), "r"(b), "r"(c));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
  io[3] = (unsigned long long)c;
}

// arm adds/adc is a 64-bit add
void asm_case_2(unsigned long long *io)
{
  unsigned int lo = (unsigned int)io[0];
  unsigned int hi = (unsigned int)io[1];
  unsigned int alo = (unsigned int)io[2];
  unsigned int ahi = (unsigned int)io[3];
  unsigned int blo = (unsigned int)io[4];
  unsigned int bhi = (unsigned int)io[5];
  __asm__("adds %0, %2, %4\n adc %1, %3, %5"
          : "=&r"(lo), "=&r"(hi)
          : "r"(alo), "r"(ahi), "r"(blo), "r"(bhi)
          : "cc");
  io[0] = (unsigned long long)lo;
  io[1] = (unsigned long long)hi;
  io[2] = (unsigned long long)alo;
  io[3] = (unsigned long long)ahi;
  io[4] = (unsigned long long)blo;
  io[5] = (unsigned long long)bhi;
}

// arm and/orr/eor combine bits
void asm_case_3(unsigned long long *io)
{
  unsigned int r = (unsigned int)io[0];
  unsigned int a = (unsigned int)io[1];
  unsigned int b = (unsigned int)io[2];
  unsigned int c = (unsigned int)io[3];
  unsigned int d = (unsigned int)io[4];
  __asm__("and %0, %1, %2\n orr %0, %0, %3\n eor %0, %0, %4"
          : "=&r"(r)
          : "r"(a), "r"(b), "r"(c), "r"(d));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
  io[3] = (unsigned long long)c;
  io[4] = (unsigned long long)d;
}

// arm cmp and conditional move
void asm_case_4(unsigned long long *io)
{
  unsigned int r = (unsigned int)io[0];
  unsigned int a = (unsigned int)io[1];
  unsigned int b = (unsigned int)io[2];
  __asm__("cmp %1, %2\n movhi %0, #1\n movls %0, #0"
          : "=r"(r)
          : "r"(a), "r"(b)
          : "cc");
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
}

// arm ldr and str move a word
void asm_case_5(unsigned long long *io)
{
  unsigned int a = (unsigned int)io[0];
  unsigned int b = (unsigned int)io[1];
  unsigned int t = (unsigned int)io[2];
  __asm__ __volatile__("ldr %0, [%1]\n str %0, [%2]"
                       : "=&r"(t)
                       : "r"(&a), "r"(&b)
                       : "memory");
  io[0] = (unsigned long long)a;
  io[1] = (unsigned long long)b;
  io[2] = (unsigned long long)t;
}

// arm lsl/lsr shift
void asm_case_6(unsigned long long *io)
{
  unsigned int r = (unsigned int)io[0];
  unsigned int a = (unsigned int)io[1];
  unsigned int b = (unsigned int)io[2];
  unsigned int c = (unsigned int)io[3];
  __asm__("lsl %0, %1, %2\n lsr %0, %0, %3"
          : "=&r"(r)
          : "r"(a), "r"(b), "r"(c));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
  io[3] = (unsigned long long)c;
}

// arm bic clears bits
void asm_case_7(unsigned long long *io)
{
  unsigned int r = (unsigned int)io[0];
  unsigned int a = (unsigned int)io[1];
  unsigned int b = (unsigned int)io[2];
  __asm__("bic %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
}

// arm rsb reverse-subtracts
void asm_case_8(unsigned long long *io)
{
  unsigned int r = (unsigned int)io[0];
  unsigned int a = (unsigned int)io[1];
  unsigned int b = (unsigned int)io[2];
  __asm__("rsb %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
}

int main(void)
{
  {
    unsigned long long io[4] = {
      0xc2a7af9eab79b005ULL, 0xffULL, 0x2ULL, 0x6ffe6666fa72766dULL};
    asm_case_0(io);
    __CPROVER_assert(
      io[0] == 0xab79b0ffULL && io[1] == 0xffULL && io[2] == 0xab79b0ffULL &&
        io[3] == 0x0ULL,
      "arm ldrex/orr/strex set a bit (atomic set), vector 0");
  }
  {
    unsigned long long io[4] = {
      0x8000000000000000ULL,
      0x8000000000000000ULL,
      0xae54d49633f89bafULL,
      0xcc5604a33a481fd2ULL};
    asm_case_0(io);
    __CPROVER_assert(
      io[0] == 0x0ULL && io[1] == 0x0ULL && io[2] == 0x0ULL && io[3] == 0x0ULL,
      "arm ldrex/orr/strex set a bit (atomic set), vector 1");
  }
  {
    unsigned long long io[4] = {
      0xadb4bded0a6cc878ULL,
      0x248a141c7ccb3b72ULL,
      0xb5d23309b6d2590dULL,
      0x33756584e354bbe7ULL};
    asm_case_0(io);
    __CPROVER_assert(
      io[0] == 0x7eeffb7aULL && io[1] == 0x7ccb3b72ULL &&
        io[2] == 0x7eeffb7aULL && io[3] == 0x0ULL,
      "arm ldrex/orr/strex set a bit (atomic set), vector 2");
  }
  {
    unsigned long long io[4] = {
      0xc2b9546e0f0220f3ULL,
      0xf1d5effedcda26fbULL,
      0x7fffffffULL,
      0xb8d3af23681c2889ULL};
    asm_case_1(io);
    __CPROVER_assert(
      io[0] == 0xf4bdfe71ULL && io[1] == 0xdcda26fbULL &&
        io[2] == 0x7fffffffULL && io[3] == 0x681c2889ULL,
      "arm add and subtract, vector 0");
  }
  {
    unsigned long long io[4] = {
      0xc60f8fe0a6269527ULL,
      0x32f6ffa49275dc84ULL,
      0x7d7ef810cfc3dc1ULL,
      0xbf30555ab55f5d1fULL};
    asm_case_1(io);
    __CPROVER_assert(
      io[0] == 0xea12bd26ULL && io[1] == 0x9275dc84ULL &&
        io[2] == 0xcfc3dc1ULL && io[3] == 0xb55f5d1fULL,
      "arm add and subtract, vector 1");
  }
  {
    unsigned long long io[4] = {
      0xb3d8c88ab7063e8dULL,
      0xefe90ebcbcb30e03ULL,
      0xffffffffULL,
      0xed25d1989c8d81a9ULL};
    asm_case_1(io);
    __CPROVER_assert(
      io[0] == 0x20258c59ULL && io[1] == 0xbcb30e03ULL &&
        io[2] == 0xffffffffULL && io[3] == 0x9c8d81a9ULL,
      "arm add and subtract, vector 2");
  }
  {
    unsigned long long io[6] = {
      0xe638bca46bd70d89ULL,
      0x2ULL,
      0x2ULL,
      0x17d967b89f01d73dULL,
      0x82974e236f761b03ULL,
      0x7fULL};
    asm_case_2(io);
    __CPROVER_assert(
      io[0] == 0x6f761b05ULL && io[1] == 0x9f01d7bcULL && io[2] == 0x2ULL &&
        io[3] == 0x9f01d73dULL && io[4] == 0x6f761b03ULL && io[5] == 0x7fULL,
      "arm adds/adc is a 64-bit add, vector 0");
  }
  {
    unsigned long long io[6] = {
      0x6bcc7b9e0a546c01ULL,
      0xffffffffULL,
      0x9541937ec1bfc7abULL,
      0x80000000ULL,
      0xef512c58c835156fULL,
      0xe685acb714786e96ULL};
    asm_case_2(io);
    __CPROVER_assert(
      io[0] == 0x89f4dd1aULL && io[1] == 0x94786e97ULL &&
        io[2] == 0xc1bfc7abULL && io[3] == 0x80000000ULL &&
        io[4] == 0xc835156fULL && io[5] == 0x14786e96ULL,
      "arm adds/adc is a 64-bit add, vector 1");
  }
  {
    unsigned long long io[6] = {
      0x8644a1e6d2818addULL,
      0xef828079a78b6244ULL,
      0x4a13b9da9f4e53bbULL,
      0x19ec4413125e5cfbULL,
      0xa51bdbee16d2b9aeULL,
      0xffULL};
    asm_case_2(io);
    __CPROVER_assert(
      io[0] == 0xb6210d69ULL && io[1] == 0x125e5dfaULL &&
        io[2] == 0x9f4e53bbULL && io[3] == 0x125e5cfbULL &&
        io[4] == 0x16d2b9aeULL && io[5] == 0xffULL,
      "arm adds/adc is a 64-bit add, vector 2");
  }
  {
    unsigned long long io[5] = {
      0x38b1f9a35c2855baULL,
      0x8a0cb201725c5338ULL,
      0xb0652c5806a310a8ULL,
      0x808332e379bd40dbULL,
      0xe586f6e1167ff12eULL};
    asm_case_3(io);
    __CPROVER_assert(
      io[0] == 0x6dc2a1d5ULL && io[1] == 0x725c5338ULL &&
        io[2] == 0x6a310a8ULL && io[3] == 0x79bd40dbULL &&
        io[4] == 0x167ff12eULL,
      "arm and/orr/eor combine bits, vector 0");
  }
  {
    unsigned long long io[5] = {
      0xffULL,
      0xb7a413d48183cf4eULL,
      0x872808db18a381eULL,
      0x89c40189aec7d882ULL,
      0x3ab70d7151d4fc15ULL};
    asm_case_3(io);
    __CPROVER_assert(
      io[0] == 0xfe13249bULL && io[1] == 0x8183cf4eULL &&
        io[2] == 0xb18a381eULL && io[3] == 0xaec7d882ULL &&
        io[4] == 0x51d4fc15ULL,
      "arm and/orr/eor combine bits, vector 1");
  }
  {
    unsigned long long io[5] = {
      0x3785478d706735ULL,
      0xffULL,
      0x7fULL,
      0x62fbfdc8c535c306ULL,
      0x7fffffffULL};
    asm_case_3(io);
    __CPROVER_assert(
      io[0] == 0xbaca3c80ULL && io[1] == 0xffULL && io[2] == 0x7fULL &&
        io[3] == 0xc535c306ULL && io[4] == 0x7fffffffULL,
      "arm and/orr/eor combine bits, vector 2");
  }
  {
    unsigned long long io[3] = {
      0xb8004092f9e22b92ULL, 0xab4d6d46b16b38cbULL, 0xc5cc618b30146b25ULL};
    asm_case_4(io);
    __CPROVER_assert(
      io[0] == 0x1ULL && io[1] == 0xb16b38cbULL && io[2] == 0x30146b25ULL,
      "arm cmp and conditional move, vector 0");
  }
  {
    unsigned long long io[3] = {
      0xc662866ad84cf328ULL, 0x8000000000000000ULL, 0xffffffffffffffffULL};
    asm_case_4(io);
    __CPROVER_assert(
      io[0] == 0x0ULL && io[1] == 0x0ULL && io[2] == 0xffffffffULL,
      "arm cmp and conditional move, vector 1");
  }
  {
    unsigned long long io[3] = {
      0xd85ee36626a12990ULL, 0x816ffbff11966d8bULL, 0x0ULL};
    asm_case_4(io);
    __CPROVER_assert(
      io[0] == 0x1ULL && io[1] == 0x11966d8bULL && io[2] == 0x0ULL,
      "arm cmp and conditional move, vector 2");
  }
  {
    unsigned long long io[3] = {
      0x662e0001e6f57713ULL, 0xf1657729e04a52fdULL, 0x4ce92b19fe991d62ULL};
    asm_case_5(io);
    __CPROVER_assert(
      io[0] == 0xe6f57713ULL && io[1] == 0xe6f57713ULL &&
        io[2] == 0xe6f57713ULL,
      "arm ldr and str move a word, vector 0");
  }
  {
    unsigned long long io[3] = {
      0x2dca9d6ea967229bULL, 0xe4a66e6e92989e7dULL, 0x350b8f5dcea6fb83ULL};
    asm_case_5(io);
    __CPROVER_assert(
      io[0] == 0xa967229bULL && io[1] == 0xa967229bULL &&
        io[2] == 0xa967229bULL,
      "arm ldr and str move a word, vector 1");
  }
  {
    unsigned long long io[3] = {
      0xabc0ff65a92da05dULL, 0x4c075f1f0b493f1aULL, 0x7d9cf46457162242ULL};
    asm_case_5(io);
    __CPROVER_assert(
      io[0] == 0xa92da05dULL && io[1] == 0xa92da05dULL &&
        io[2] == 0xa92da05dULL,
      "arm ldr and str move a word, vector 2");
  }
  {
    unsigned long long io[4] = {
      0x71985eb13a883919ULL, 0x7fffffffffffffffULL, 0x1cULL, 0x1fULL};
    asm_case_6(io);
    __CPROVER_assert(
      io[0] == 0x1ULL && io[1] == 0xffffffffULL && io[2] == 0x1cULL &&
        io[3] == 0x1fULL,
      "arm lsl/lsr shift, vector 0");
  }
  {
    unsigned long long io[4] = {
      0x4f18c672fa42fe7cULL, 0x120984629605b44fULL, 0x14ULL, 0x0ULL};
    asm_case_6(io);
    __CPROVER_assert(
      io[0] == 0x44f00000ULL && io[1] == 0x9605b44fULL && io[2] == 0x14ULL &&
        io[3] == 0x0ULL,
      "arm lsl/lsr shift, vector 1");
  }
  {
    unsigned long long io[4] = {
      0xfd64b9e5bd0edb5aULL, 0x25406c9bc1a6364ULL, 0x0ULL, 0x12ULL};
    asm_case_6(io);
    __CPROVER_assert(
      io[0] == 0x2f06ULL && io[1] == 0xbc1a6364ULL && io[2] == 0x0ULL &&
        io[3] == 0x12ULL,
      "arm lsl/lsr shift, vector 2");
  }
  {
    unsigned long long io[3] = {
      0xd6bc0d35ccec83e4ULL, 0x4fb0d79be3130b3fULL, 0x2d65a8a1cf4ce48eULL};
    asm_case_7(io);
    __CPROVER_assert(
      io[0] == 0x20130b31ULL && io[1] == 0xe3130b3fULL &&
        io[2] == 0xcf4ce48eULL,
      "arm bic clears bits, vector 0");
  }
  {
    unsigned long long io[3] = {
      0x0ULL, 0xdae98f58edaf5ddULL, 0xbb5f3ec2488a958cULL};
    asm_case_7(io);
    __CPROVER_assert(
      io[0] == 0x86506051ULL && io[1] == 0x8edaf5ddULL &&
        io[2] == 0x488a958cULL,
      "arm bic clears bits, vector 1");
  }
  {
    unsigned long long io[3] = {
      0x8bcb7f1085e0c86ULL, 0x3dc7152f30428c31ULL, 0x12257820e6b755cfULL};
    asm_case_7(io);
    __CPROVER_assert(
      io[0] == 0x10408830ULL && io[1] == 0x30428c31ULL &&
        io[2] == 0xe6b755cfULL,
      "arm bic clears bits, vector 2");
  }
  {
    unsigned long long io[3] = {
      0x71f2223ff559a0f9ULL, 0xc447a6fbb54b9c52ULL, 0xf34de6440ce23540ULL};
    asm_case_8(io);
    __CPROVER_assert(
      io[0] == 0x579698eeULL && io[1] == 0xb54b9c52ULL && io[2] == 0xce23540ULL,
      "arm rsb reverse-subtracts, vector 0");
  }
  {
    unsigned long long io[3] = {
      0x2444fb01d3bdc021ULL, 0xfc66ce02975f8fb3ULL, 0xffULL};
    asm_case_8(io);
    __CPROVER_assert(
      io[0] == 0x68a0714cULL && io[1] == 0x975f8fb3ULL && io[2] == 0xffULL,
      "arm rsb reverse-subtracts, vector 1");
  }
  {
    unsigned long long io[3] = {
      0xca7d4a778a0b60a5ULL, 0x38e3ee6142044392ULL, 0xa67f5e58956140eULL};
    asm_case_8(io);
    __CPROVER_assert(
      io[0] == 0x4751d07cULL && io[1] == 0x42044392ULL &&
        io[2] == 0x8956140eULL,
      "arm rsb reverse-subtracts, vector 2");
  }
  return 0;
}
