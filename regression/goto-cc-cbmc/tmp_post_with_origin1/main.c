int main(int argc, char **argv)
{
  int *ptr;
  ptr = malloc(2);
  ptr += 2;
  int v = *ptr++;
  return 0;
}
