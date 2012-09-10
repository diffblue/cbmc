struct teststr {
   int a;
   int b;
   int c;
};

struct teststr str_array[] = {
  { .a = 3 },
  { .b = 4 }
};

int main()
{
  assert(str_array[0].a==3);
  assert(str_array[0].b==0);
  assert(str_array[1].b==4);

  int x;
  
  // this also exists (GCC)
  str_array[0] = (struct teststr){ .a=1, .c=x };
  assert(str_array[0].a==1);
  assert(str_array[0].b==0);
  assert(str_array[0].c==x);
}
