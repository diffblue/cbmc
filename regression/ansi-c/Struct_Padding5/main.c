#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef _MSC_VER

// Visual Studio
__declspec(align(8)) struct flowi
{
  char ch;
  char flexible[];
};

#else

// GCC
struct flowi
{
  char ch;
  char flexible[];
} __attribute__((__aligned__(64/8)));

#endif

// in either case, the struct gets bigger!
STATIC_ASSERT(sizeof(struct flowi)==8);

#ifdef __GNUC__
STATIC_ASSERT(__builtin_offsetof(struct flowi, flexible)==1);
#endif

// bit-fields are very evil
#pragma pack(push, 1)
struct bit_field0
{
  int i : 23;
};

struct bit_field1
{
  int i : 1;
  unsigned int j : 1;
  // in MSC, it matters that the underlying type changes!
  short c : 1;
};

struct bit_field2
{
  int i : 23;
  char ch;
};
#pragma pack(pop)

struct bit_field3
{
  int i : 23;
  char ch;
};

#ifdef _MSC_VER
STATIC_ASSERT(sizeof(struct bit_field0) == 4);
STATIC_ASSERT(sizeof(struct bit_field1) == 6);
STATIC_ASSERT(sizeof(struct bit_field2) == 5);
STATIC_ASSERT(sizeof(struct bit_field3) == 8);
#else
STATIC_ASSERT(sizeof(struct bit_field0) == 3);
STATIC_ASSERT(sizeof(struct bit_field1) == 1);
STATIC_ASSERT(sizeof(struct bit_field2) == 4);
STATIC_ASSERT(sizeof(struct bit_field3) == 4);
#endif

int main()
{
}
