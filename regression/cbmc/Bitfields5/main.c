union
{
  unsigned five : 5;
  char *a;
  unsigned one : 1;
} b = {8};
int main()
{
  __CPROVER_assert(0, "");
}
