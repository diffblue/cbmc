// Flexible array members in unions are allowed as an extension on Windows.

union U
{
  int n;
  char flexible_array_member[];
};

int main()
{
  union U u;
  u.n = 42;
}
