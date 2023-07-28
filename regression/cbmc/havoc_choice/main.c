#include <assert.h>
#include <stdbool.h>

bool nondet_bool();

int main()
{
  char a = 'a';
  char b = 'b';
  char c = 'c';
  char d = 'd';

  char *p =
    nondet_bool() ? (nondet_bool() ? &a : &b) : (nondet_bool() ? &c : &d);

  __CPROVER_havoc_object(p);

  if(p == &a)
    assert(a == 'a');
  else
    assert(a == 'a');

  if(p == &b)
    assert(b == 'b');
  else
    assert(b == 'b');

  if(p == &c)
    assert(c == 'c');
  else
    assert(c == 'c');

  if(p == &d)
    assert(d == 'd');
  else
    assert(d == 'd');
}
