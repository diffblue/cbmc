// C11 6.7.2.1 §18 allows flexible array members in structures, but not in
// unions. This file exercises the named-union form (the other, anonymous
// form is covered by union_flexible_array_member.c).

union U
{
  int n;
  char flexible_array_member[];
};
