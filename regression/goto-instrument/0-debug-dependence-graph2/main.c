
typedef struct {
  int *a;
  int b;
} mystruct_t;

int main()
{
  int x;
  int y;
  mystruct_t ms;

  ms.a = &x;
  ms.a = &y;

  *(ms.a) = 1;

  return 0;
}

