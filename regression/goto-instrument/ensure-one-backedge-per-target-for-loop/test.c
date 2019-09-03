int main(int argc, char **argv)
{
  for(int i = 0; i < 10; ++i)
  {
    ++i;
    if(i == 5)
      continue;
    --i;
  }
}
