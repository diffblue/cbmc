void f1()
{
  int array1[4];

  char *p = (char *)array1;

  for(unsigned i = 0; i < sizeof(array1); i++)
    *(p + i) = i;

  assert(
    array1[0] == 0x03020100 /* little endian */ ||
    array1[0] == 0x00010203 /* big endian */);
  assert(
    array1[1] == 0x07060504 /* little endian */ ||
    array1[1] == 0x04050607 /* big endian */);
}

void f2()
{
  int array2[4];

  char *p = (char *)array2;

  array2[1] = 0x0200;
  p[4] = 1;

  assert(
    array2[1] == 0x0201 /* little endian */ ||
    array2[1] == 0x01000200 /* big endian */);
}

int main()
{
  f1();
  f2();
}
