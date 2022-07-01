#include <assert.h>

struct PtrWrapper
{
  char *value_c;
};

void fn(struct PtrWrapper wrapper)
{
  assert(wrapper.value_c == 'B');
}

void indirect(int (*fn_ptr)(char *), char *data)
{
  fn_ptr(data);
  assert(0);
}

int main()
{
  struct PtrWrapper wrapper;
  wrapper.value_c = 'A';

  int (*alias)(char *) = (int (*)(char *))fn;
  indirect(alias, &wrapper.value_c);
}
