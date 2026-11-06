#include <assert.h>

#ifdef __GNUC__
int x = 0, y = 0, w = 0, order_check = 0;

// Constructor with priority argument; name chosen to make sure lexicographic
// ordering does not incidentally produce the correct sequence.
__attribute__((constructor(101))) void z_init_priority(void)
{
  x = 1;
}

// Constructor with priority argument
__attribute__((constructor(102))) void y_init_priority2(void)
{
  assert(x == 1);
  x = 2;
}

// Destructor with higher priority argument; runs before destructor(201) because
// destructors run in descending priority order.
__attribute__((destructor(202))) void fini_priority2(void)
{
  // The unprioritised destructor runs first.
  assert(w == 4);
  // No prioritised destructor has run yet.
  assert(order_check == 0);
  order_check = 202;
}

// Destructor with priority argument
__attribute__((destructor(201))) void fini_priority(void)
{
  assert(w == 4);
  // destructor(202) must have run before destructor(201).
  assert(order_check == 202);
  order_check = 201;
  y = 2;
}

// Constructor without priority (should still work, have lowest priority)
__attribute__((constructor)) void x_init_no_priority(void)
{
  assert(x == 2);
  x = 3;
}

// Destructor without priority (should still work, has highest priority)
__attribute__((destructor)) void fini_no_priority(void)
{
  w = 4;
}
#endif

int main()
{
#ifdef __GNUC__
  // All constructors should have run before main
  assert(x == 3);
  // Destructors haven't run yet
  assert(y == 0);
  assert(w == 0);
  assert(order_check == 0);
#endif
  return 0;
}
