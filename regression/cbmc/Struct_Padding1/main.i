struct my_struct1
{
  int i;
  char ch;

  struct
  {
    // this gets padded
    int j;
  };

  // Bit-fields do not get padded in between,
  // but fill up an integer!
  unsigned bf1:1;
  unsigned bf2:28;
} xx1 =
{
  1, 2, { .j=3 }
};

struct my_struct2
{
  int i;
  char ch[4];

  // no padding needed
  int j;

  char ch2;
  // there may be end-padding!
} xx2;

struct my_struct3 {
   unsigned int bit_field : 1;
   int i;
} xx3= { 1, 2 };

int some_array1[(sizeof(xx1)==4+1+3+4+4) ? 1 : -1];
int some_array2[(sizeof(xx2)==4+4+4+4) ? 1 : -1];

int main()
{
  __CPROVER_assert(xx1.i==1, "");
  __CPROVER_assert(xx1.ch==2, "");
  __CPROVER_assert(xx1.j==3, "");

  // let's probe the padding
  char *p=&xx1.ch;
  __CPROVER_assert(p[0]==2, "");
  __CPROVER_assert(p[1]==0, "");
  __CPROVER_assert(p[2]==0, "");
  __CPROVER_assert(p[3]==0, "");

  __CPROVER_assert(xx3.bit_field==1, "");
  __CPROVER_assert(xx3.i==2, "");
}
