#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

struct Z1
{
  char ch;
  int i:3;
  char ch2;
  // there is end-of-struct padding because of the int
};

STATIC_ASSERT(_Alignof(struct Z1) == _Alignof(int));

#ifdef _MSC_VER
STATIC_ASSERT(sizeof(struct Z1) == 4 + 4 + 4);
#else
STATIC_ASSERT(sizeof(struct Z1) == 1 + 1 + 1 + 1);
#ifdef __GNUC__
STATIC_ASSERT(__builtin_offsetof(struct Z1, ch2) == 2);
#endif
#endif

#pragma pack(push, 1)
struct Z1_packed
{
  char ch;
  int i : 3;
  char ch2;
  // there is no end-of-struct padding
};
#pragma pack(pop)

STATIC_ASSERT(_Alignof(struct Z1_packed) == 1);

#ifdef _MSC_VER
STATIC_ASSERT(sizeof(struct Z1_packed) == 1 + 4 + 1);
#else
STATIC_ASSERT(sizeof(struct Z1_packed) == 1 + 1 + 1);
#ifdef __GNUC__
STATIC_ASSERT(__builtin_offsetof(struct Z1_packed, ch2) == 2);
#endif
#endif

struct Z2
{
  char ch;
  char i:3;
  char ch2;
  // there is no end-of-struct padding
};

STATIC_ASSERT(sizeof(struct Z2) == 1 + 1 + 1);

#pragma pack(push, 1)
struct Z2_packed
{
  char ch;
  char i : 3;
  char ch2;
  // there is no end-of-struct padding
};
#pragma pack(pop)

STATIC_ASSERT(sizeof(struct Z2_packed) == 1 + 1 + 1);

struct Z3
{
  char ch;
  int i : 3; // padded by MSVC, not by gcc/clang
};

#ifdef _MSC_VER
STATIC_ASSERT(sizeof(struct Z3) == 4 + 4);
#else
STATIC_ASSERT(sizeof(struct Z3) == 1 + 1 + 2);
#endif

#pragma pack(push, 1)
struct Z3_packed
{
  char ch;
  int i : 3; // padded by MSVC, not by gcc/clang
};
#pragma pack(pop)

#ifdef _MSC_VER
STATIC_ASSERT(sizeof(struct Z3_packed) == 1 + 4);
#else
STATIC_ASSERT(sizeof(struct Z3_packed) == 1 + 1);
#endif

struct Z4
{
  int i;
  long long int x; // pads to 8
  char ch; // 7 end-of-struct padding
};

STATIC_ASSERT(sizeof(struct Z4) == 4 + 4 + 8 + 1 + 7);

#pragma pack(push, 1)
struct Z4_packed
{
  int i;
  long long int x; // no padding
  char ch;         // no end-of-struct padding
};
#pragma pack(pop)

STATIC_ASSERT(sizeof(struct Z4_packed) == 4 + 8 + 1);

struct Z5
{
  char ch;
  long long int x[]; // pads to 8, but has no size
};

STATIC_ASSERT(sizeof(struct Z5) == 8);

#pragma pack(push, 1)
struct Z5_packed
{
  char ch;
  long long int x[]; // pads to 8, but has no size
};
#pragma pack(pop)

STATIC_ASSERT(sizeof(struct Z5_packed) == 1);

struct Z6
{
  char ch;
  int i : 16; // padded to int by MSVC, to short by gcc/clang
};

#ifdef _MSC_VER
STATIC_ASSERT(sizeof(struct Z6) == 4 + 4);
#else
STATIC_ASSERT(sizeof(struct Z6) == 1 + 1 + 2);
#endif

#pragma pack(push, 1)
struct Z6_packed
{
  char ch;
  int i : 16; // padded to int by MSC, but not aligned
};
#pragma pack(pop)

#ifdef _MSC_VER
STATIC_ASSERT(sizeof(struct Z6_packed) == 1 + 4);
#else
STATIC_ASSERT(sizeof(struct Z6_packed) == 1 + 2);
#endif

int main()
{
}
