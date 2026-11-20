// AArch64 inline assembly that is interpreted exactly. The expected values were
// observed with an emulator.

// aarch64 ldxr/add/stxr set a bit (atomic_set llsc)
void asm_case_0(unsigned long long *io)
{
  unsigned int m = (unsigned int)io[0];
  unsigned int v = (unsigned int)io[1];
  unsigned int tmp = (unsigned int)io[2];
  unsigned int res = (unsigned int)io[3];
  __asm__ __volatile__(
    "1: ldxr %w0, [%2]\n"
    "   orr  %w0, %w0, %w3\n"
    "   stxr %w1, %w0, [%2]\n"
    "   cbnz %w1, 1b\n"
    : "=&r"(tmp), "=&r"(res)
    : "r"(&m), "r"(v)
    : "memory");
  io[0] = (unsigned long long)m;
  io[1] = (unsigned long long)v;
  io[2] = (unsigned long long)tmp;
  io[3] = (unsigned long long)res;
}

// aarch64 ldadd is an atomic add (LSE)
void asm_case_1(unsigned long long *io)
{
  unsigned int m = (unsigned int)io[0];
  unsigned int v = (unsigned int)io[1];
  unsigned int old = (unsigned int)io[2];
  __asm__ __volatile__("ldadd %w2, %w0, [%1]"
                       : "=r"(old)
                       : "r"(&m), "r"(v)
                       : "memory");
  io[0] = (unsigned long long)m;
  io[1] = (unsigned long long)v;
  io[2] = (unsigned long long)old;
}

// aarch64 ldset ORs into memory and returns the old value (LSE)
void asm_case_2(unsigned long long *io)
{
  unsigned long m = (unsigned long)io[0];
  unsigned long v = (unsigned long)io[1];
  unsigned long old = (unsigned long)io[2];
  __asm__ __volatile__("ldset %2, %0, [%1]"
                       : "=r"(old)
                       : "r"(&m), "r"(v)
                       : "memory");
  io[0] = (unsigned long long)m;
  io[1] = (unsigned long long)v;
  io[2] = (unsigned long long)old;
}

// aarch64 swp exchanges a register and memory (LSE)
void asm_case_3(unsigned long long *io)
{
  unsigned int m = (unsigned int)io[0];
  unsigned int v = (unsigned int)io[1];
  unsigned int old = (unsigned int)io[2];
  __asm__ __volatile__("swp %w2, %w0, [%1]"
                       : "=r"(old)
                       : "r"(&m), "r"(v)
                       : "memory");
  io[0] = (unsigned long long)m;
  io[1] = (unsigned long long)v;
  io[2] = (unsigned long long)old;
}

// aarch64 cas compares and swaps (LSE)
void asm_case_4(unsigned long long *io)
{
  unsigned int m = (unsigned int)io[0];
  unsigned int cmp = (unsigned int)io[1];
  unsigned int newv = (unsigned int)io[2];
  __asm__ __volatile__("cas %w0, %w2, [%1]"
                       : "+r"(cmp)
                       : "r"(&m), "r"(newv)
                       : "memory");
  io[0] = (unsigned long long)m;
  io[1] = (unsigned long long)cmp;
  io[2] = (unsigned long long)newv;
}

// aarch64 add then subtract
void asm_case_5(unsigned long long *io)
{
  unsigned long r = (unsigned long)io[0];
  unsigned long a = (unsigned long)io[1];
  unsigned long b = (unsigned long)io[2];
  unsigned long c = (unsigned long)io[3];
  __asm__("add %0, %1, %2\n sub %0, %0, %3"
          : "=&r"(r)
          : "r"(a), "r"(b), "r"(c));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
  io[3] = (unsigned long long)c;
}

// aarch64 and with a shifted register
void asm_case_6(unsigned long long *io)
{
  unsigned long r = (unsigned long)io[0];
  unsigned long a = (unsigned long)io[1];
  unsigned long b = (unsigned long)io[2];
  __asm__("and %0, %1, %2, lsl #4" : "=r"(r) : "r"(a), "r"(b));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
}

// aarch64 cmp and cset compute a predicate
void asm_case_7(unsigned long long *io)
{
  unsigned long r = (unsigned long)io[0];
  unsigned long a = (unsigned long)io[1];
  unsigned long b = (unsigned long)io[2];
  __asm__("cmp %1, %2\n cset %0, hi" : "=r"(r) : "r"(a), "r"(b) : "cc");
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
}

// aarch64 ldr and str move a word through memory
void asm_case_8(unsigned long long *io)
{
  unsigned int a = (unsigned int)io[0];
  unsigned int b = (unsigned int)io[1];
  unsigned int t = (unsigned int)io[2];
  __asm__ __volatile__("ldr %w0, [%1]\n str %w0, [%2]"
                       : "=&r"(t)
                       : "r"(&a), "r"(&b)
                       : "memory");
  io[0] = (unsigned long long)a;
  io[1] = (unsigned long long)b;
  io[2] = (unsigned long long)t;
}

// aarch64 eor and orr combine bits
void asm_case_9(unsigned long long *io)
{
  unsigned long r = (unsigned long)io[0];
  unsigned long a = (unsigned long)io[1];
  unsigned long b = (unsigned long)io[2];
  unsigned long c = (unsigned long)io[3];
  __asm__("eor %0, %1, %2\n orr %0, %0, %3"
          : "=&r"(r)
          : "r"(a), "r"(b), "r"(c));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
  io[3] = (unsigned long long)c;
}

// aarch64 lsl and lsr shift
void asm_case_10(unsigned long long *io)
{
  unsigned long r = (unsigned long)io[0];
  unsigned long a = (unsigned long)io[1];
  unsigned long b = (unsigned long)io[2];
  unsigned long c = (unsigned long)io[3];
  __asm__("lsl %0, %1, %2\n lsr %0, %0, %3"
          : "=&r"(r)
          : "r"(a), "r"(b), "r"(c));
  io[0] = (unsigned long long)r;
  io[1] = (unsigned long long)a;
  io[2] = (unsigned long long)b;
  io[3] = (unsigned long long)c;
}

// aarch64 movz/movk build a constant
void asm_case_11(unsigned long long *io)
{
  unsigned long r = (unsigned long)io[0];
  __asm__("movz %0, #0x1234\n movk %0, #0xabcd, lsl #16" : "=r"(r));
  io[0] = (unsigned long long)r;
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
      "aarch64 ldxr/add/stxr set a bit (atomic_set llsc), vector 0");
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
      "aarch64 ldxr/add/stxr set a bit (atomic_set llsc), vector 1");
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
      "aarch64 ldxr/add/stxr set a bit (atomic_set llsc), vector 2");
  }
  {
    unsigned long long io[3] = {
      0xc2b9546e0f0220f3ULL, 0xf1d5effedcda26fbULL, 0x7fffffffULL};
    asm_case_1(io);
    __CPROVER_assert(
      io[0] == 0xebdc47eeULL && io[1] == 0xdcda26fbULL && io[2] == 0xf0220f3ULL,
      "aarch64 ldadd is an atomic add (LSE), vector 0");
  }
  {
    unsigned long long io[3] = {
      0xb8d3af23681c2889ULL, 0xc60f8fe0a6269527ULL, 0x32f6ffa49275dc84ULL};
    asm_case_1(io);
    __CPROVER_assert(
      io[0] == 0xe42bdb0ULL && io[1] == 0xa6269527ULL && io[2] == 0x681c2889ULL,
      "aarch64 ldadd is an atomic add (LSE), vector 1");
  }
  {
    unsigned long long io[3] = {
      0x7d7ef810cfc3dc1ULL, 0xbf30555ab55f5d1fULL, 0xb3d8c88ab7063e8dULL};
    asm_case_1(io);
    __CPROVER_assert(
      io[0] == 0xc25b9ae0ULL && io[1] == 0xb55f5d1fULL && io[2] == 0xcfc3dc1ULL,
      "aarch64 ldadd is an atomic add (LSE), vector 2");
  }
  {
    unsigned long long io[3] = {0xe638bca46bd70d89ULL, 0x2ULL, 0x2ULL};
    asm_case_2(io);
    __CPROVER_assert(
      io[0] == 0xe638bca46bd70d8bULL && io[1] == 0x2ULL &&
        io[2] == 0xe638bca46bd70d89ULL,
      "aarch64 ldset ORs into memory and returns the old value (LSE), vector "
      "0");
  }
  {
    unsigned long long io[3] = {
      0x17d967b89f01d73dULL, 0x82974e236f761b03ULL, 0x7fULL};
    asm_case_2(io);
    __CPROVER_assert(
      io[0] == 0x97df6fbbff77df3fULL && io[1] == 0x82974e236f761b03ULL &&
        io[2] == 0x17d967b89f01d73dULL,
      "aarch64 ldset ORs into memory and returns the old value (LSE), vector "
      "1");
  }
  {
    unsigned long long io[3] = {
      0x6bcc7b9e0a546c01ULL, 0xffffffffULL, 0x9541937ec1bfc7abULL};
    asm_case_2(io);
    __CPROVER_assert(
      io[0] == 0x6bcc7b9effffffffULL && io[1] == 0xffffffffULL &&
        io[2] == 0x6bcc7b9e0a546c01ULL,
      "aarch64 ldset ORs into memory and returns the old value (LSE), vector "
      "2");
  }
  {
    unsigned long long io[3] = {
      0x38b1f9a35c2855baULL, 0x8a0cb201725c5338ULL, 0xb0652c5806a310a8ULL};
    asm_case_3(io);
    __CPROVER_assert(
      io[0] == 0x725c5338ULL && io[1] == 0x725c5338ULL &&
        io[2] == 0x5c2855baULL,
      "aarch64 swp exchanges a register and memory (LSE), vector 0");
  }
  {
    unsigned long long io[3] = {
      0x808332e379bd40dbULL, 0xe586f6e1167ff12eULL, 0xffULL};
    asm_case_3(io);
    __CPROVER_assert(
      io[0] == 0x167ff12eULL && io[1] == 0x167ff12eULL &&
        io[2] == 0x79bd40dbULL,
      "aarch64 swp exchanges a register and memory (LSE), vector 1");
  }
  {
    unsigned long long io[3] = {
      0xb7a413d48183cf4eULL, 0x872808db18a381eULL, 0x89c40189aec7d882ULL};
    asm_case_3(io);
    __CPROVER_assert(
      io[0] == 0xb18a381eULL && io[1] == 0xb18a381eULL &&
        io[2] == 0x8183cf4eULL,
      "aarch64 swp exchanges a register and memory (LSE), vector 2");
  }
  {
    unsigned long long io[3] = {0x5ULL, 0x5ULL, 0x9ULL};
    asm_case_4(io);
    __CPROVER_assert(
      io[0] == 0x9ULL && io[1] == 0x5ULL && io[2] == 0x9ULL,
      "aarch64 cas compares and swaps (LSE), vector 0");
  }
  {
    unsigned long long io[3] = {0x5ULL, 0x7ULL, 0x9ULL};
    asm_case_4(io);
    __CPROVER_assert(
      io[0] == 0x5ULL && io[1] == 0x5ULL && io[2] == 0x9ULL,
      "aarch64 cas compares and swaps (LSE), vector 1");
  }
  {
    unsigned long long io[3] = {0x0ULL, 0x0ULL, 0x1ULL};
    asm_case_4(io);
    __CPROVER_assert(
      io[0] == 0x1ULL && io[1] == 0x0ULL && io[2] == 0x1ULL,
      "aarch64 cas compares and swaps (LSE), vector 2");
  }
  {
    unsigned long long io[3] = {0xdeadbeefULL, 0xdeadbeefULL, 0x1ULL};
    asm_case_4(io);
    __CPROVER_assert(
      io[0] == 0x1ULL && io[1] == 0xdeadbeefULL && io[2] == 0x1ULL,
      "aarch64 cas compares and swaps (LSE), vector 3");
  }
  {
    unsigned long long io[4] = {
      0x662e0001e6f57713ULL,
      0xf1657729e04a52fdULL,
      0x4ce92b19fe991d62ULL,
      0x2dca9d6ea967229bULL};
    asm_case_5(io);
    __CPROVER_assert(
      io[0] == 0x108404d5357c4dc4ULL && io[1] == 0xf1657729e04a52fdULL &&
        io[2] == 0x4ce92b19fe991d62ULL && io[3] == 0x2dca9d6ea967229bULL,
      "aarch64 add then subtract, vector 0");
  }
  {
    unsigned long long io[4] = {
      0xe4a66e6e92989e7dULL,
      0x350b8f5dcea6fb83ULL,
      0xabc0ff65a92da05dULL,
      0x4c075f1f0b493f1aULL};
    asm_case_5(io);
    __CPROVER_assert(
      io[0] == 0x94c52fa46c8b5cc6ULL && io[1] == 0x350b8f5dcea6fb83ULL &&
        io[2] == 0xabc0ff65a92da05dULL && io[3] == 0x4c075f1f0b493f1aULL,
      "aarch64 add then subtract, vector 1");
  }
  {
    unsigned long long io[4] = {
      0x7d9cf46457162242ULL, 0x7fULL, 0x8000000000000000ULL, 0x80000000ULL};
    asm_case_5(io);
    __CPROVER_assert(
      io[0] == 0x7fffffff8000007fULL && io[1] == 0x7fULL &&
        io[2] == 0x8000000000000000ULL && io[3] == 0x80000000ULL,
      "aarch64 add then subtract, vector 2");
  }
  {
    unsigned long long io[3] = {
      0x71985eb13a883919ULL, 0x7fffffffffffffffULL, 0xc42192ad002d93dcULL};
    asm_case_6(io);
    __CPROVER_assert(
      io[0] == 0x42192ad002d93dc0ULL && io[1] == 0x7fffffffffffffffULL &&
        io[2] == 0xc42192ad002d93dcULL,
      "aarch64 and with a shifted register, vector 0");
  }
  {
    unsigned long long io[3] = {
      0xffffffffULL, 0x4f18c672fa42fe7cULL, 0x120984629605b44fULL};
    asm_case_6(io);
    __CPROVER_assert(
      io[0] == 0x18462060424470ULL && io[1] == 0x4f18c672fa42fe7cULL &&
        io[2] == 0x120984629605b44fULL,
      "aarch64 and with a shifted register, vector 1");
  }
  {
    unsigned long long io[3] = {
      0x4eb832d5079a2474ULL, 0x0ULL, 0xfd64b9e5bd0edb5aULL};
    asm_case_6(io);
    __CPROVER_assert(
      io[0] == 0x0ULL && io[1] == 0x0ULL && io[2] == 0xfd64b9e5bd0edb5aULL,
      "aarch64 and with a shifted register, vector 2");
  }
  {
    unsigned long long io[3] = {
      0xd6bc0d35ccec83e4ULL, 0x4fb0d79be3130b3fULL, 0x2d65a8a1cf4ce48eULL};
    asm_case_7(io);
    __CPROVER_assert(
      io[0] == 0x1ULL && io[1] == 0x4fb0d79be3130b3fULL &&
        io[2] == 0x2d65a8a1cf4ce48eULL,
      "aarch64 cmp and cset compute a predicate, vector 0");
  }
  {
    unsigned long long io[3] = {
      0x0ULL, 0xdae98f58edaf5ddULL, 0xbb5f3ec2488a958cULL};
    asm_case_7(io);
    __CPROVER_assert(
      io[0] == 0x0ULL && io[1] == 0xdae98f58edaf5ddULL &&
        io[2] == 0xbb5f3ec2488a958cULL,
      "aarch64 cmp and cset compute a predicate, vector 1");
  }
  {
    unsigned long long io[3] = {
      0x8bcb7f1085e0c86ULL, 0x3dc7152f30428c31ULL, 0x12257820e6b755cfULL};
    asm_case_7(io);
    __CPROVER_assert(
      io[0] == 0x1ULL && io[1] == 0x3dc7152f30428c31ULL &&
        io[2] == 0x12257820e6b755cfULL,
      "aarch64 cmp and cset compute a predicate, vector 2");
  }
  {
    unsigned long long io[3] = {
      0x71f2223ff559a0f9ULL, 0xc447a6fbb54b9c52ULL, 0xf34de6440ce23540ULL};
    asm_case_8(io);
    __CPROVER_assert(
      io[0] == 0xf559a0f9ULL && io[1] == 0xf559a0f9ULL &&
        io[2] == 0xf559a0f9ULL,
      "aarch64 ldr and str move a word through memory, vector 0");
  }
  {
    unsigned long long io[3] = {
      0x2444fb01d3bdc021ULL, 0xfc66ce02975f8fb3ULL, 0xffULL};
    asm_case_8(io);
    __CPROVER_assert(
      io[0] == 0xd3bdc021ULL && io[1] == 0xd3bdc021ULL &&
        io[2] == 0xd3bdc021ULL,
      "aarch64 ldr and str move a word through memory, vector 1");
  }
  {
    unsigned long long io[3] = {
      0xca7d4a778a0b60a5ULL, 0x38e3ee6142044392ULL, 0xa67f5e58956140eULL};
    asm_case_8(io);
    __CPROVER_assert(
      io[0] == 0x8a0b60a5ULL && io[1] == 0x8a0b60a5ULL &&
        io[2] == 0x8a0b60a5ULL,
      "aarch64 ldr and str move a word through memory, vector 2");
  }
  {
    unsigned long long io[4] = {
      0x80000000ULL, 0x85c6eecdbd37c64dULL, 0xe051fbafdcfbbb5eULL, 0x7fULL};
    asm_case_9(io);
    __CPROVER_assert(
      io[0] == 0x6597156261cc7d7fULL && io[1] == 0x85c6eecdbd37c64dULL &&
        io[2] == 0xe051fbafdcfbbb5eULL && io[3] == 0x7fULL,
      "aarch64 eor and orr combine bits, vector 0");
  }
  {
    unsigned long long io[4] = {
      0x1ULL, 0x7fULL, 0x7e0269edac79ca6eULL, 0xffffffffffffffffULL};
    asm_case_9(io);
    __CPROVER_assert(
      io[0] == 0xffffffffffffffffULL && io[1] == 0x7fULL &&
        io[2] == 0x7e0269edac79ca6eULL && io[3] == 0xffffffffffffffffULL,
      "aarch64 eor and orr combine bits, vector 1");
  }
  {
    unsigned long long io[4] = {
      0xffULL,
      0xfc5d96cc82bdb472ULL,
      0x7fffffffffffffffULL,
      0x2355aca2a0edf46dULL};
    asm_case_9(io);
    __CPROVER_assert(
      io[0] == 0xa3f7edb3fdefffedULL && io[1] == 0xfc5d96cc82bdb472ULL &&
        io[2] == 0x7fffffffffffffffULL && io[3] == 0x2355aca2a0edf46dULL,
      "aarch64 eor and orr combine bits, vector 2");
  }
  {
    unsigned long long io[4] = {0xd29b8652db47179aULL, 0x1ULL, 0x3ULL, 0x3fULL};
    asm_case_10(io);
    __CPROVER_assert(
      io[0] == 0x0ULL && io[1] == 0x1ULL && io[2] == 0x3ULL && io[3] == 0x3fULL,
      "aarch64 lsl and lsr shift, vector 0");
  }
  {
    unsigned long long io[4] = {
      0xd57e59721b5c3f00ULL, 0x8161ebbba4c1b5daULL, 0x1aULL, 0x24ULL};
    asm_case_10(io);
    __CPROVER_assert(
      io[0] == 0xee9306dULL && io[1] == 0x8161ebbba4c1b5daULL &&
        io[2] == 0x1aULL && io[3] == 0x24ULL,
      "aarch64 lsl and lsr shift, vector 1");
  }
  {
    unsigned long long io[4] = {
      0x5e4c1de7ba5f33e2ULL, 0x870cf5c903adeee9ULL, 0x2dULL, 0x3eULL};
    asm_case_10(io);
    __CPROVER_assert(
      io[0] == 0x2ULL && io[1] == 0x870cf5c903adeee9ULL && io[2] == 0x2dULL &&
        io[3] == 0x3eULL,
      "aarch64 lsl and lsr shift, vector 2");
  }
  {
    unsigned long long io[1] = {0x6a08e48807e06ce6ULL};
    asm_case_11(io);
    __CPROVER_assert(
      io[0] == 0xabcd1234ULL, "aarch64 movz/movk build a constant, vector 0");
  }
  return 0;
}
