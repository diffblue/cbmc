struct S
{
  explicit operator bool() const
  {
    return true;
  }
};

int main()
{
  S s;
  if(s)
  {
  }
  return 0;
}
