#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

#define G(X) _Generic((X), \
                long double: 1, \
                default: 10, \
                float: 2, \
                int: 3, \
                char: 4, \
                struct some: 5 \
             )

struct some
{
} s;

int i;
char ch;
long double ld;
short sh;

#ifdef __GNUC__
STATIC_ASSERT(G(i)==3);
STATIC_ASSERT(G(sh)==10);
STATIC_ASSERT(G(ld)==1);
STATIC_ASSERT(G(ch)==4);
STATIC_ASSERT(G(s)==5);
#else

// Visual Studio doesn't have it.

#endif

int main()
{
}
