// Default Initialization of arrays
class B
{
public:
  int i;

  B():i(1)
  {
  }
};

class A
{
public:
  B b_array[2];
  A() {}
};

B static_b_array[2];

int main()
{
  assert(static_b_array[0].i==1);
  assert(static_b_array[1].i==1);

  A a;

  assert(a.b_array[0].i==1);
  assert(a.b_array[1].i==1);

  B b_array[2];
	
  assert(b_array[0].i==1);
  assert(b_array[1].i==1);
}
