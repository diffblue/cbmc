int main()
{
  int i = 0;
  do
  {
    ++i;
    if(i == 5)
      continue;
    ++i;
  } while(i < 10);
}
