int glob;

int main()
{
  glob=-1;

  while(glob<10)
  {
    // this isn't inductive, as it fails the base case
    __CPROVER_assert(glob>=0 && glob<10, "property");

    glob++;
  }
}
