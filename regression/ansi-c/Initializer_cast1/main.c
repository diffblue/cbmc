struct S
{
  int a, b, c;
  struct T
  {
    int x, y, z;
  } sub;
};

union U
{
  int a;
  struct S s;
};

typedef int array_type[10];

int main()
{
  long l;
  struct S s;
  union U u;

  // scalar  
  l=(long){0x1};
  
  // struct
  s=(struct S){ 1, 2, 3, 4, 5, 6 };
  
  // union
  u=(union U)s;
  
  // union
  u=(union U){ 1 };
  
  // array
  const int *a=(array_type){ 1, 2, 3, 4 };
}
