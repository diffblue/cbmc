#include <assert.h>
#include <malloc.h>

struct S
{
  struct S *next;
};

struct S st;
struct S *p;
struct S *q;

void initialize()
{
  st.next = &st;
  p = &st;
  q = malloc(sizeof(struct S));
}

void checkpoint()
{
}

int main()
{
  initialize();
  checkpoint();

  assert(p == &st);
  assert(p->next == &st);
  assert(p != q);
  q->next = &st;
  assert(p == q->next);
}
