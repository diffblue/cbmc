#include <assert.h>

struct foo_st {
  int foo;
  int bar;
  int foobar;
};

int main(int argc, char **argv) {

  struct foo_st r;

  r = ((struct foo_st){1,2,3});

  assert(r.foo==1);
  assert(r.bar==2);
  assert(r.foobar==3);

  r = ((struct foo_st){ .foo=10, .foobar=30});

  assert(r.foo==10);
  assert(r.bar==0); // !
  assert(r.foobar==30);
}
