void exit(int s)
{
_EXIT:
  goto _EXIT;
}

int main()
{
  exit(1);
}
