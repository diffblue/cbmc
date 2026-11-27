extern "C" void __CPROVER_assert(bool, const char *);

// a GNU attribute after a declarator keeps the declaration's type
struct record
{
  unsigned a[4];
};

extern volatile record placed __attribute__((section(".data.placed")));
volatile record placed;

static int counter __attribute__((section(".data.counter"))) = 5;

int main()
{
  placed.a[1] = 3;
  __CPROVER_assert(placed.a[1] == 3, "struct");
  __CPROVER_assert(counter == 5 && sizeof(counter) == sizeof(int), "int");

  __CPROVER_assert(false, "WRONG (must FAIL)");
  return 0;
}
