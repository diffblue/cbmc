// Arrays over the field-sensitivity limit whose elements are themselves
// arrays of structs or pointers, and an over-limit array inside a struct that
// is an element of a small array.
struct s
{
  int *p;
  int x;
};

struct s outer_over[100][2]; // the outer array exceeds the limit
int *pointers_over[100][2];
struct s inner_over[2][100]; // the inner arrays exceed the limit

struct w
{
  struct s in[70];
} in_struct[3];

int g;

int main(void)
{
  outer_over[1][0].p = &g;
  pointers_over[1][0] = &g;
  inner_over[1][5].p = &g;
  in_struct[2].in[3].p = &g;
  __CPROVER_assert(*outer_over[1][0].p == g, "outer_over");
  __CPROVER_assert(*pointers_over[1][0] == g, "pointers_over");
  __CPROVER_assert(*inner_over[1][5].p == g, "inner_over");
  __CPROVER_assert(*in_struct[2].in[3].p == g, "in_struct");
  return 0;
}
