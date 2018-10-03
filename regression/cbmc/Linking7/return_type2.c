struct S
{
  int i;
  int j; // extra member
} some_var;

struct S *function()
{
  return &some_var;
}
