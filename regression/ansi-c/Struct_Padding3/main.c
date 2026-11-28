#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifndef __GNUC__
#define __builtin_offsetof(a, b) ((unsigned long long)&(((a *)0)->b))
#endif

#ifdef __GNUC__

struct my_struct1a {
  char ch1;
  int i; // this would normally be padded, but it won't!
  char ch2;
} __attribute__((packed));

STATIC_ASSERT(__builtin_offsetof(struct my_struct1a, i)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1a, ch2)==5);

struct my_struct1b {
  char ch1;
  // this would normally be padded, but it won't!
  int i __attribute__((packed));
  char ch2;
};

STATIC_ASSERT(__builtin_offsetof(struct my_struct1b, i)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1b, ch2)==5);

struct my_struct1c {
  char ch1;
  // this would normally be padded, but it won't!
  struct
  {
    int i;
  } sub __attribute__((packed));
  char ch2;
};

STATIC_ASSERT(__builtin_offsetof(struct my_struct1c, sub.i)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1c, ch2)==5);

struct my_struct1d {
  char ch0;
  // the next field isn't padded
  struct
  {
    char ch1;
    int i; // this _is_ padded!
  } sub __attribute__((packed));
  char ch2;
};

STATIC_ASSERT(__builtin_offsetof(struct my_struct1d, sub.ch1)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1d, sub.i)==5);
STATIC_ASSERT(__builtin_offsetof(struct my_struct1d, ch2)==9);

struct __attribute__((packed)) my_struct2 {
  char ch1;
  int i; // this would normally be padded, but it won't!
  char ch2;
};

STATIC_ASSERT(__builtin_offsetof(struct my_struct2, i)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct2, ch2)==5);

typedef unsigned int uint32_t;
typedef unsigned long long int uint64_t;

struct formatted {
  unsigned short moddate;
  uint32_t crc32 __attribute__ ((__packed__));
};

STATIC_ASSERT(__builtin_offsetof(struct formatted, crc32)==2);

typedef struct __attribute__((__packed__))
{
 uint32_t version;
} ipc_msg_hdr;

typedef struct
{
  ipc_msg_hdr hdr;
  uint32_t data_bytes;
  uint64_t terminate;
} request_state;

STATIC_ASSERT(sizeof(ipc_msg_hdr)==4);
STATIC_ASSERT(__builtin_offsetof(request_state, data_bytes)==4);
STATIC_ASSERT(__builtin_offsetof(request_state, terminate)==8);
STATIC_ASSERT(sizeof(request_state)==16);

#endif

// the alignment of long long, which is 4 with the System V ABI for i386
struct long_long_alignment
{
  char c;
  long long x;
};
#define LL_ALIGN __builtin_offsetof(struct long_long_alignment, x)

struct my_struct3 {
  char ch1;
  char ch2;
  int i1; // this should be padded for 4-byte alignment
  char ch3;
  long long i2; // this should be padded for the alignment of long long
  char ch4;
  int bf1 : 1; // MSVC pads this, the gcc/clang do not
  int bf2 : 1; // MSVC pads this, the gcc/clang do not
  int i3;    // this should be padded for 4-byte alignment
};

STATIC_ASSERT(__builtin_offsetof(struct my_struct3, ch1)==0);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, ch2)==1);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, i1)==4);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, ch3)==8);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, i2) == 8 + LL_ALIGN);
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, ch4) == 16 + LL_ALIGN);

#ifdef _MSC_VER
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, i3) == 24 + LL_ALIGN);
#else
STATIC_ASSERT(__builtin_offsetof(struct my_struct3, i3) == 20 + LL_ALIGN);
#endif

int main()
{
}
