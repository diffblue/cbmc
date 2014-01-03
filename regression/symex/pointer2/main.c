struct S1
{
  char ch0, ch1, ch2, ch3;
} my_struct1;

struct S2
{
  int i1, i2;
} my_struct2;

int main()
{
  // a pointer into a struct
  int *p=(int *)&my_struct1;

  *p=0x03020100;

  // endianness-dependent
  assert(my_struct1.ch0==0);
  assert(my_struct1.ch1==1);
  assert(my_struct1.ch2==2);
  assert(my_struct1.ch3==3);

  // same bigger
  long long int *q=(long long int *)&my_struct2;
  *q=0x200000001ull;
  assert(my_struct2.i1==1);
  assert(my_struct2.i2==2);
}
