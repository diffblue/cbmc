#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

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
__declspec(align(packed)) union some_union4
{
  int i:3;
};

#else

// bit-fields are evil
union some_union4
{
  int i:3;
} __attribute__((__packed__));

#endif

STATIC_ASSERT(sizeof(union some_union4)==sizeof(char));

int main()
{
}
