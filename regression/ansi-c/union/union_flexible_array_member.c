// C11 6.7.2.1 §18 allows flexible array members in structures,
// but not unions.

union
{
  char flexible_array_member[];
};
