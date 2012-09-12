#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

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

int main()
{
}
