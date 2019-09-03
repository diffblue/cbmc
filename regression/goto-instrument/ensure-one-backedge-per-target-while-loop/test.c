int main(int argc, char **argv)
{
  int i = 0;
  while(i < 10)
  {
    ++i;
    if(i == 5)
      continue;
    ++i;
  }
}
