#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

// C11:
// 6.3.1.2 Boolean type
// When any scalar value is converted to _Bool, the result is 0 if the value
// compares equal to 0; otherwise, the result is 1.

STATIC_ASSERT((_Bool)10);
STATIC_ASSERT(((_Bool)10)==1);
STATIC_ASSERT(!(_Bool)0);
STATIC_ASSERT((_Bool)0.1);
STATIC_ASSERT(!(_Bool)(int)0.1);
STATIC_ASSERT(!(_Bool)0.0);
STATIC_ASSERT(!(_Bool)-0.0);

// array to _Bool
char my_array[10];
STATIC_ASSERT((_Bool)my_array);

// pointer to _Bool
char my_array[10];
STATIC_ASSERT((_Bool)(int *)1);

int main()
{
}
