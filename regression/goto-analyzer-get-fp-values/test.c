#include <assert.h>


// this is here to avoid resolving function
// pointers to functions from the standard library
// by accident to make the tests more precise
struct Dummy_t{} dummy;

typedef int (*fptr_t)(int, struct Dummy_t);

fptr_t get_f(void);

void fptr_is_g_or_h(fptr_t fptr)
{
  assert(fptr(10, dummy) <= 10);
}

void fptr_is_f(fptr_t fptr)
{
  assert(fptr(10, dummy) == 11);
}

void fptr_is_top(fptr_t fptr)
{
  int result = fptr(10, dummy);
  assert(result >= 9 && result <= 11);
  assert(result == 9);
  assert(result == 10);
  assert(result == 11);
}

// this is not called at all, which
// makes it bottom
void fptr_is_bottom(fptr_t fptr)
{
  assert(fptr(10, dummy) >= 10);
}

fptr_t nondet_fptr(void);

int f(int x, struct Dummy_t dummy);
int g(int x, struct Dummy_t dummy);
int h(int x, struct Dummy_t);

int main(void)
{
  fptr_is_g_or_h(g);
  fptr_is_g_or_h(h);
  
  fptr_is_f(f);

  fptr_is_top(nondet_fptr());

  // fptr_is_bottom is not called at all,
  // which is what makes it bottom
  return 0;
}

int f(int x, struct Dummy_t dummy)
{
  return x + 1;
}

int g(int x, struct Dummy_t dummy)
{
  return x;
}

int h(int x, struct Dummy_t dummy)
{
  return x - 1;
}
