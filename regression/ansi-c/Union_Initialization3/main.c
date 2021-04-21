union {
  int a;
  struct
  {
    unsigned b : 4;
    unsigned c : 4;
  };
} u1 = {.b = 5, .c = 1};

#ifndef _MSC_VER
union {
  int;
  struct
  {
    unsigned b : 4;
    unsigned c : 4;
  };
} u2 = {.b = 5, .c = 1};
#endif

int main()
{
}
