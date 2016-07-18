struct S
{
  int x;
  struct S *next;
} s;


void f(struct S *sptr1, struct S *sptr2)
{
  sptr1->next=sptr2;
  
  // main::1::s[].next = { <main$$1$$s[0l], 16, struct S> }
  //   but it can also be NULL here
  
  s.next->x=1;
}

int main()
{
  struct S s[2];
 
  f(&s[0], &s[1]);
  
  return 0;
}
