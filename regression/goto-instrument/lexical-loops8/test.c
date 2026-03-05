int main()
{
  int i = 0;
  int count;

  while(i < 10)
  {
    if(count == 5)
      break;
    ++i;
    if(count % 7)
      continue;
    count--;
  }

  return count;
}
