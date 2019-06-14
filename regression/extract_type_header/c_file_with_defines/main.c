struct A
{
  int a;
  int b;
};

typedef struct A myStruct;

#define address a

#define bucket(X, Y, Z)                                                        \
  if(X)                                                                        \
  {                                                                            \
    Z = get_b(X) == Y;                                                         \
  }                                                                            \
  else                                                                         \
  {                                                                            \
    Z = get_default() == Y;                                                    \
  }

#ifndef address
#  define address 1
#endif

int get_b(myStruct *s)
{
  return s->b;
}

int get_default()
{
  return 0;
}

int main()
{
  myStruct aStruct = {123, 456};
  __CPROVER_assert(aStruct.address == 123, "address");
  int z;
  bucket(&aStruct, 456, z);
  __CPROVER_assert(z, "bucket");
}
