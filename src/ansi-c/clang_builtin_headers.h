__gcc_v4sf __builtin_shufflevector(__gcc_v4sf, __gcc_v4sf, ...);

__gcc_v2di __builtin_ia32_undef128(void);
__gcc_v4di __builtin_ia32_undef256(void);
__gcc_v8di __builtin_ia32_undef512(void);

void __builtin_nontemporal_store();
void __builtin_nontemporal_load();

int __builtin_flt_rounds(void);

// clang-format off
unsigned char __builtin_rotateleft8(unsigned char, unsigned char);
unsigned short __builtin_rotateleft16(unsigned short, unsigned short);
unsigned int __builtin_rotateleft32(unsigned int, unsigned int);
unsigned long long __builtin_rotateleft64(unsigned long long, unsigned long long);

unsigned char __builtin_rotateright8(unsigned char, unsigned char);
unsigned short __builtin_rotateright16(unsigned short, unsigned short);
unsigned int __builtin_rotateright32(unsigned int, unsigned int);
unsigned long long __builtin_rotateright64(unsigned long long, unsigned long long);
// clang-format on
