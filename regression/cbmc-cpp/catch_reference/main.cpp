int main()
{
  try
  {
    return 0;
  }
  catch(const int &e)
  {
    return 1;
  }
  catch(...)
  {
    return 2;
  }
}
