typedef enum : unsigned
{
  X
} my_enum1;

enum my_enum2 : unsigned
{
  Y
};

struct S
{
  enum my_enum2 : unsigned a;
  enum my_enum2 : unsigned b : 2;
};

int main()
{
  enum my_enum2 : unsigned enum_var1;
}
