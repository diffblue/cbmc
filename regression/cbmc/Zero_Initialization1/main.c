// gcc allows the following

union U my_u;

union U
{
  int some;  
};

struct S my_s;

struct S
{
  int some;
};

enum E my_e;

enum E { ASD };

int main()
{
  assert(my_u.some==0);
  assert(my_s.some==0);
  assert(my_e==0);
}
