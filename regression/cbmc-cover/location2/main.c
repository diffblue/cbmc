void *memset(void *, int, __CPROVER_size_t);

#define BUFLEN 100

static void *(*const volatile memset_func)(void *, int, __CPROVER_size_t) =
  memset;

int main()
{
  char buffer[BUFLEN];
  memset_func(&buffer, 0, BUFLEN);
}
