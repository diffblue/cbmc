int main(int argc, char **argv)
{
  for(int i = 0; i < 4; i++)
  {
    char c;
    __CPROVER_input("c", c);
    if(c == 42)
      return 0;
  }
  return 1;
}
