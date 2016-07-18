
int main()
{
  typedef struct {
    int a;
    int b;
  } some_struct_t;

  some_struct_t ss;
  ss.a = 3;
  ss.b = 137;

  some_struct_t *ssp;
  ssp = &ss;
  ssp->b = 138;

  return 0;
}

