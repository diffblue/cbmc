void f(char *p)
{
  p[1]=1;
}

int main () 
{
  char dummy[10];
  f(dummy);
}
