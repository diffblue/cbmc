int main (void)
{
  int i = 0;

  while (i < 0) i++;
  while (i < 0.0f) i++;
  while (i < (int)0U) i++;
  while (i < (int)0.0f) i++;

  return 0;
}
