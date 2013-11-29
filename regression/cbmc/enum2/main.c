enum flags { FLAG1, FLAG2, FLAG3, FLAG4 };

enum bool {false, true};
enum bool skipping;

int main()
{
  int height = (1 << FLAG4);
  assert(8 == height);

  // this should work
  skipping = 2 >= 1; // <-- conversion _Bool -> enum bool
  assert(skipping);

  // conversion _Bool -> enum in initializer
  enum { FOO = 1 == 1 };
  enum { BAR = 1 == 0 };
  assert(FOO==1);
  assert(BAR==0);

  return 0;
}
