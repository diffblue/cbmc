enum { E1, E2, E3 } a;

struct Z
{
  enum { E4=4, E5=5, E6=6, EPLUS=+0 } b;
};

// these are good as constants
int array[E5];

int main()
{
  int integer;
  
  a=E2;
  assert(a==1);
  
  assert(E4==4);
  assert(sizeof(array)==sizeof(int)*5);
  
  integer=a;
  assert(integer==1);
}

enum l { A, B, C };

void fun (int a) {}

void fun2()
{
  enum l L;
  enum l L2=A;
  fun((int) L);
}
