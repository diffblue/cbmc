#include <assert.h>

// Constant static initializers given by compound literals, which the C front
// end turns into members of those literals, including through unions,
// bit-fields and arrays.
// This is the shape of the kernel's dynamic-debug _ddebug descriptor, whose
// .key union is initialised from the STATIC_KEY_FALSE_INIT compound literal.
// Before member-of-compound-literal simplification, the type checker rejected
// it with "expected constant expression".
typedef struct
{
  int counter;
} atomic_t;
struct static_key
{
  atomic_t enabled;
  union
  {
    unsigned long type;
    void *entries;
  };
};
struct kf
{
  struct static_key key;
};
struct kt
{
  struct static_key key;
};
struct B
{
  signed x : 3;
  unsigned y : 5;
  char c;
  short s;
};
struct A
{
  char c;
  int arr[3];
  struct B b;
};
struct dd
{
  const char *f;
  unsigned flags;
  union
  {
    struct kt t;
    struct kf f;
  } key;
  struct B bf;
  struct A a;
};
#define KF(v, t)                                                               \
  (struct kf)                                                                  \
  {                                                                            \
    .key = {.enabled = {v}, {.type = t} }                                      \
  }
static struct dd d = {
  .f = "x",
  .flags = 1,
  .key.f = (KF(5, 7ul)),
  .bf = (struct B){.x = -2, .y = 17, .c = 'q', .s = -3},
  .a = (struct A){'z', {4, 5, 6}, {-1, 3, 'r', 9}},
};
struct dd d2 = {.key.f = (KF(5, 7ul))};
int main(void)
{
  static struct dd l = {.key.f = (KF(-4, 0xfffffffful))};
  assert(d.key.f.key.enabled.counter == 5);
  assert(d.key.f.key.type == 7);
  assert(d.key.t.key.enabled.counter == 5);
  assert(d.key.t.key.type == 7);
  assert(d.bf.x == -2 && d.bf.y == 17 && d.bf.c == 'q' && d.bf.s == -3);
  assert(
    d.a.c == 'z' && d.a.arr[2] == 6 && d.a.b.x == -1 && d.a.b.y == 3 &&
    d.a.b.c == 'r' && d.a.b.s == 9);
  assert(d2.key.t.key.enabled.counter == 5);
  assert(l.key.f.key.enabled.counter == -4);
  assert(l.key.t.key.type == 0xfffffffful);
  d.key.f.key.enabled.counter = 11;
  assert(d.key.t.key.enabled.counter == 11);
  return 0;
}
