#define STATIC_ASSERT(condition) \
  int array##__LINE__[(condition) ? 1 : -1]

#ifdef __GNUC__

int  x   __attribute__ ((__vector_size__ (12), __may_alias__));
int  x2   __attribute__ ((__may_alias__));
int  x3   __attribute__ ((__may_alias__, __vector_size__ (12)));

STATIC_ASSERT(sizeof(x)==12);
STATIC_ASSERT(sizeof(x2)==sizeof(int));
STATIC_ASSERT(sizeof(x3)==12);

#endif

int main(int argc, char* argv[])
{
  return 0;
}
