int main(int argc, char **argv)
{
  char *arr_ptr[2];
  char *ptr = malloc(2);
  ptr += 2;
  *arr_ptr = ptr;
  char v = *(arr_ptr[0])++;
  return 0;
}
