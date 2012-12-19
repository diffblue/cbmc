
enum { E1, E2, E3 } a;

class Z
{
public:
  enum { E4=4, E5=5, E6=6 };

  // these are good as constants
  int array[E5];
} z;

static_assert(Z::E4==4, "value of Z::E4");
static_assert(sizeof(z.array)==sizeof(int)*5, "size of z.array");
static_assert(((int)E1)==0, "value of E1");
static_assert(((int)E2)==1, "value of E2");

int main()
{
  a=E2;
  int integer;
  integer=a;
}
