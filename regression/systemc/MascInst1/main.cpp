#include <cassert>

typedef unsigned uint;

class mv_int_char {
    int first;
    char second;
  public:
    mv_int_char(int x, char y) {first = x; second = y;}
    void assign(int &x, char &y) {x = first; y = second;}
};

class array_5_int {
  public:
    int elt[5];
};

mv_int_char init_mv()
{
  char z=1;
  mv_int_char m(0,z);
  return m;
}

void test_mv()
{
// TODO: doesn't work
//  char z=1;
//  mv_int_char m(0,z);

   mv_int_char m = init_mv();

  int x;
  char y;
  m.assign(x,y);

  assert(x==0);
  assert(y==1);
}

array_5_int init_array()
{
  array_5_int a;
  for(int i=0;i<5;i++)
    a.elt[i] = i*i;
  return a;
}

void test_array()
{
  array_5_int a = init_array();
  assert(a.elt[4]==16);
}

int main (int argc, char *argv[])
{
  test_mv();
  test_array();
  return 0;
}
