// Returning a value makes the front-end emit an OUTPUT (an OTHER instruction)
// in __CPROVER__start, which used to crash --show-global-may-alias.
int g;
int *p;
int main()
{
  p = &g;
  g = 1;
  return *p;
}
