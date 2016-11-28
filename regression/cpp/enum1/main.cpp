enum E123_tag { E1, E2, E3 } a;

class Z
{
public:
  enum { E4=4, E5=5, E6=6 };

  // these are good as constants
  int array[E5];
} z;

static_assert(Z::E4==4, "value of Z::E4");
static_assert(sizeof(z.array)==sizeof(int)*5, "size of z.array");
static_assert(E1==0, "value of E1");
static_assert(E2==1, "value of E2");
static_assert(E123_tag(0)==E1, "value of E123_tag(0)");
static_assert((E123_tag)0==E1, "value of E123_tag(0)");

int main()
{
  a=E2;
  int integer;
  integer=a;
}

// They can go into namespaces
namespace whereever { enum some_tag { something }; }

enum whereever::some_tag whatnot = whereever::something;
