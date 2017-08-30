int main()
{
  goto bla;

  for(int i=0; i<5; ++i)
  {
bla: i=10;
  }
}
