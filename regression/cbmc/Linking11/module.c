// TU2: a different struct S (with members x and y)
// During linking, this struct S will be renamed because it conflicts
// with TU1's struct S. The parameter type of g must be updated to
// refer to TU1's struct S.
struct S
{
  int x;
  int y;
};

// Declaration matching TU1's g — parameter type refers to this TU's struct S,
// which will be renamed during linking.
int g(struct S *p)
{
  return p->x;
}
