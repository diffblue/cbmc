#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1]

STATIC_ASSERT(((long int)0x7FFFFFFFL)>0);

STATIC_ASSERT(sizeof(1)==sizeof(int));
STATIC_ASSERT(sizeof(100000000)==4);
STATIC_ASSERT(sizeof(1L)==sizeof(long));
STATIC_ASSERT(sizeof(1LL)==8);
STATIC_ASSERT(sizeof(1000000000000)==8);

int main()
{
}
