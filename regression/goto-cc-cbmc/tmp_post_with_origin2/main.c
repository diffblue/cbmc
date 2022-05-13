int main(int argc, char **argv)
{
  char **pptr;
  pptr = malloc(8);
  char *ptr = malloc(2);
  ptr += 2;
  *pptr = ptr;
  char v = *(*pptr++)++;
  return 0;
}
