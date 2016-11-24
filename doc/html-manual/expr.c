int *ptr;

int main(void) {
  if (ptr)
    *ptr = 0;
  if (!ptr)
    *ptr = 1;
}
