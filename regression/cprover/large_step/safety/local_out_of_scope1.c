int main()
{
  int *p;

  {
    int x;
    p = &x;
    *p; // ok
  }

  //  *p; // unsafe
}
