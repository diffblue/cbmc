#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];    

#ifdef __GNUC__

typedef int __attribute__ ((vector_size (16))) a, b;
typedef int c, d __attribute__ ((vector_size (16)));
typedef int e __attribute__ ((vector_size (16))), f;

STATIC_ASSERT(sizeof(a)==16 && sizeof(b)==16);
STATIC_ASSERT(sizeof(c)==sizeof(int) && sizeof(d)==16);
STATIC_ASSERT(sizeof(e)==16 && sizeof(f)==sizeof(int));

#endif

int main()
{
}
