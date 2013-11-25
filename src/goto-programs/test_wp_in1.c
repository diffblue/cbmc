// test input for test_wp

int x, *p, a[100], i;

struct S
{
  int f1, f2;
} s, t;

void f()
{
  x++; assert(x==1);
  *p=1; assert(x==1);
  (*p)++; assert(x==1);
  x++; assert(s.f1==1);
  *p=1; assert(s.f1==1);
  s.f1++; assert(s.f1==1);
  a[10]++; assert(a[10]==1);
  a[20]++; assert(a[10]==1);
  a[20]++; assert(a[i]==1);
  *p=1; assert(a[i]==1);
  *p=1; assert(*p==1);
  x=1; assert(*p==1);
  s=t; assert(s.f1==1);
}
