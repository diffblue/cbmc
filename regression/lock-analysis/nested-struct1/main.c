
struct S
{
  struct T
  {
    int x;
    struct S *next;
  } t;

} s;


void f(struct S *sptr1, struct S *sptr2)
{
  sptr1->t.next=sptr2;
}

int main()
{
  struct S s1, s2;

  f(&s1, &s2);

  return 0;
}
