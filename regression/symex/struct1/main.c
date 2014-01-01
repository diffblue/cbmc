struct inner_struct
{
  int a, b, c;
};

struct top_level
{
  int x, y, z;
  struct inner_struct inner;
};

struct top_level my_s = { 1, 2, 3, 4, 5, 6 };
struct inner_struct my_inner;

int main()
{
  assert(my_s.inner.a==4);
  assert(my_inner.a==0);
  my_inner.a++;
  assert(my_inner.a==1);
  my_s.inner=my_inner; // assigns all of 'inner'
  assert(my_s.inner.a==1);
}
