#include <assert.h>

struct void_ptr
{
  void *ptr;
};

void havoc_struct(struct void_ptr *s);

int main(void)
{
  struct void_ptr s;
  havoc_struct(&s);
  if(s.ptr)
    *(char *)s.ptr = 42;
  assert(!s.ptr || *(char *)s.ptr == 42);
  return 0;
}
