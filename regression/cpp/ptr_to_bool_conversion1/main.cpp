struct S
{
  operator bool() const
  {
    return true;
  }
};

int *get_ptr();

int main()
{
  // pointer-to-bool standard conversion
  int *p = get_ptr();
  if(p)
  {
  }

  // struct-to-bool via user-defined conversion operator
  S s;
  if(s)
  {
  }

  return 0;
}
