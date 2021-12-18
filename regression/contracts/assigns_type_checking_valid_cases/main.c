#include <stdlib.h>

int *x;
int y;

struct blob
{
  int allocated;
};
struct buf
{
  int *data;
  size_t len;
  struct blob aux;
};

void foo1(int a) __CPROVER_assigns()
{
  a = 0;
}

void foo2(int *b) __CPROVER_assigns()
{
  b = NULL;
}

void foo3(int a, int *b) __CPROVER_assigns(x, y)
{
  b = NULL;
  x = malloc(sizeof(*x));
  y = 0;
}

void foo4(int a, int *b, int *c) __CPROVER_requires(c != NULL)
  __CPROVER_requires(x != NULL) __CPROVER_assigns(*c, *x)
{
  b = NULL;
  *c = 0;
  *x = 0;
}

void foo5(struct buf buffer) __CPROVER_assigns()
{
  buffer.data = NULL;
  buffer.len = 0;
}

void foo6(struct buf *buffer) __CPROVER_assigns(buffer->data, buffer->len)
{
  buffer->data = malloc(sizeof(*(buffer->data)));
  *(buffer->data) = 1;
  buffer->len = 1;
}

void foo7(int a, struct buf *buffer) __CPROVER_assigns(*buffer)
{
  buffer->data = malloc(sizeof(*(buffer->data)));
  *(buffer->data) = 1;
  buffer->len = 1;
}

void foo8(int array[]) __CPROVER_assigns(__CPROVER_POINTER_OBJECT(array))
{
  array[0] = 1;
  array[1] = 1;
  array[2] = 1;
  array[3] = 1;
  array[4] = 1;
  array[5] = 1;
  array[6] = 1;
  array[7] = 1;
  array[8] = 1;
  array[9] = 1;
}

void foo9(int array[]) __CPROVER_assigns()
{
  int *new_array = NULL;
  array = new_array;
}

void foo10(struct buf *buffer) __CPROVER_requires(buffer != NULL)
  __CPROVER_assigns(buffer->len, buffer->aux.allocated)
{
  buffer->len = 0;
  buffer->aux.allocated = 0;
}

int main()
{
  int n;
  int *m;
  int *o = malloc(sizeof(*o));
  struct buf buffer;
  int array_call[10] = {0};
  foo1(n);
  foo2(&n);
  foo3(n, m);
  foo4(n, m, o);
  foo5(buffer);
  foo6(&buffer);
  foo7(n, &buffer);
  foo8(array_call);
  foo9(array_call);
  foo10(&buffer);
  return 0;
}
