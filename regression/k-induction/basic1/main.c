int glob;

int main()
{
  int loc=0;

  while(glob!=1000)
  {
    if(glob<10) glob++;
    if(loc<10) loc++;
    // this is one-inductive
    __CPROVER_assert(glob==loc, "property");
  }
}
