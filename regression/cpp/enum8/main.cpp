#include <cassert>

enum E1 { e1 } e1_var;
enum E2 { e2 } e2_var;

// let's check enum overloading

int f(int) { return 0; }
int f(E1) { return 1; }
int f(E2) { return 2; }

int g(int) { return 0; }
int g(E1) { return 1; }

// within a bit-field

struct some_struct
{
  int i : 10;
  E1 e1 : 10;
  E2 e2 : 10;
} some_struct_var;

int main()
{
  assert(f(0)==0);
  assert(f(e1)==1);
  assert(f(e2)==2);
  assert(f(e1_var)==1);
  assert(f(e2_var)==2);

  assert(g(0)==0);
  assert(g(e1)==1);
  assert(g(e2)==0);
  assert(g(e1_var)==1);
  assert(g(e2_var)==0);

  assert(f(some_struct_var.i)==0);
  assert(f(some_struct_var.e1)==1);
  assert(f(some_struct_var.e2)==2);
}

