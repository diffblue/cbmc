#define NULL 0

int x;
int y = 23;
const int z = 23;
const int array[] = { 5, 6, 7, 8};

struct s { int x; };
struct s s1;
struct s s2 = { 23 };
const struct s s3 = { 23 };

struct t { int x; const int y; };
struct t t1;
struct t t2 = { 23, 23 };
const struct t t3 = { 23, 23 };

struct u { const int x; };
struct u u1;
struct u u2 = { 23 };
const struct u u3 = { 23 };

struct list { const int datum; struct list * next; };

// The point of this is that cbmc needs to correctly handle
// the embedded datum int the nested struct which is const,
// while not falling into infinite recursion from the 
// recursive field.
struct another_list {
    struct a_list { 
        struct a_list * next; 
        const int datum; 
    } embedded;
    int a;
};

struct contains_pointer {  int x; int *p; };
// const int *p : declare p as pointer to const int
struct contains_pointer_to_const {  int x; const int *p; };
// int * const p : declare p as const pointer to int
struct contains_constant_pointer {  int x; int * const p; };
// this should cause a bug
struct contains_pointer_to_const_point {  int x; int * y; int * const p; };

struct contains_pointer a[3] = { {23, &x}, {23, &x}, {23, &x} };
struct contains_constant_pointer b[3] = { {23, &y}, {23, &y}, {23, &y} };
struct contains_pointer_to_const c[3] = { {23, &z}, {23, &z}, {23, &z} };
struct contains_pointer_to_const_point d[3]= { {23, &y, &z}, {23, &y, &z}, {23, &y, &z} };

struct list node = {10, NULL};

struct another_list one_list = {{10, NULL}, 5};

typedef int Int;
typedef const int Const_Int;

const Int p = 23;
Const_Int q = 23;


#include <assert.h>

int main (int argc, char **argv) 
{
  struct list linked_list = {5, &node};

  /* Pass normally but fail with nondet-static */
  assert(x == 0);
  assert(y == 23);
  assert(s1.x == 0);
  assert(s2.x == 23);
  assert(a[0].x == 23);
  assert(a[0].p == &x);
  assert(c[2].x == 23);
  assert(c[2].p == &z);
  
  /* Should still pass */
  assert(z == 23);
  assert(s3.x == 23);
  assert(t1.y == 0);
  assert(t2.y == 23);
  assert(t3.x == 23);
  assert(t3.y == 23);
  assert(u1.x == 0);
  assert(u2.x == 23);
  assert(u3.x == 23);
  assert(p == 23);
  assert(q == 23);
  assert(t1.x == 0);
  assert(t2.x == 23);
  assert(b[1].x == 23);
  assert(b[1].p == &y);
  assert(d[1].y == &y);
  assert(linked_list.datum == 5);
  assert(linked_list.next->datum == 10);
  assert(one_list.a == 5);
  assert(array[1] == 6);
  
  return 0;
}
