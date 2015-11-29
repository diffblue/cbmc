#define STATIC_ASSERT(condition) \
  int some_array##__LINE__[(condition) ? 1 : -1];

STATIC_ASSERT((void*)0==(void*)(1-1));

int main()
{
  assert((void*)0==(void*)('a'-'a'));
  return 0;
}
