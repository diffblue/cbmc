#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

#ifdef _MSC_VER

// Visual Studio
__declspec(align(8)) union some_union1
{
  char some;
};

#else

// GCC
union some_union1
{
  char some;
} __attribute__((__aligned__(8)));

#endif

// in either case, the union gets bigger!
STATIC_ASSERT(sizeof(union some_union1)==8);

// bit-fields are evil
union some_union2
{
  char ch:3;
};

STATIC_ASSERT(sizeof(union some_union2)==sizeof(char));

// bit-fields are evil
union some_union3
{
  int i:3;
};

STATIC_ASSERT(sizeof(union some_union3)==sizeof(int));

#ifdef _MSC_VER

// bit-fields are evil
#pragma pack(push, 1)
union some_union4
{
  int i:23;
};
#pragma pack(pop)

// Visual Studio ignores the 'packed'
STATIC_ASSERT(sizeof(union some_union4)==sizeof(int));
STATIC_ASSERT(__alignof(union some_union4) == 1);

#else

// bit-fields are evil
union some_union4
{
  int i:23;
} __attribute__((__packed__));

STATIC_ASSERT(sizeof(union some_union4)==3);
STATIC_ASSERT(_Alignof(union some_union4) == 1);

#endif

union some_union5
{
  int i;
};

#ifdef _MSC_VER
STATIC_ASSERT(__alignof(union some_union5) == 4);
#else
STATIC_ASSERT(_Alignof(union some_union5) == 4);
#endif

#ifdef _MSC_VER
#pragma pack(push, 1)
union some_union6 {
  int i;
};
#pragma pack(pop)

// Packing may affect alignment
STATIC_ASSERT(__alignof(union some_union6) == 1);
#else
union some_union6
{
  int i;
} __attribute__((__packed__));

// Packing may affect alignment
STATIC_ASSERT(_Alignof(union some_union6)==1);
#endif

int main()
{
}
