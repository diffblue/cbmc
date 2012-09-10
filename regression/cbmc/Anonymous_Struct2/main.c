struct X
{
  struct
  {
    int i;
  };

  struct
  {
    int j;
  };
};

struct Y
{
  struct
  {
    int i;
  };

  struct
  {
    int j;
  };
};

struct S_struct
{
  union U_union {
    int x, y;
  };
  
  int z;
} s;

struct S_struct s2={ { .x=1 }, .z=1 };

int main()
{
  s.x=1;
  s.y=2;
  s.z=3;
  
  assert(s2.y==1);
  assert(s2.z==1);
}
