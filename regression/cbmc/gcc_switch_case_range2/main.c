typedef enum
{
  VALUE_1,
  VALUE_2,
  VALUE_3,
  VALUE_4
} values;

int main()
{
  unsigned x;
  switch(x)
  {
  case VALUE_1:
    __CPROVER_assert(0, "0 works");
    break;
#ifdef __GNUC__
  case VALUE_2 ... 3:
#else
  case VALUE_2:
  case VALUE_3:
  case VALUE_4:
#endif
    __CPROVER_assert(0, "... works");
    break;
  default:
    __CPROVER_assert(0, "default works");
    break;
  }

  return 0;
}
