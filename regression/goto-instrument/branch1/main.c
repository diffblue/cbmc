const char *last;
void marker(const char *id)
{
  last = id;
}
int main()
{
  int x;
  if(x > 0)
    x = 1;
  else
    x = 2;
  __CPROVER_assert(x != 1 || last[0] == 'n', "then branch: jump not taken");
  __CPROVER_assert(x != 2 || last[0] == 't', "else branch: jump taken");
  return 0;
}
