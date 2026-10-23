// Typedef and using aliases should be usable as scopes to access
// static members and nested types.

struct A
{
  static const int value = 42;
  typedef int nested_type;
};

typedef A my_typedef;

int x = my_typedef::value;

using my_using = A;

int y = my_using::value;

int main()
{
  return x + y;
}
