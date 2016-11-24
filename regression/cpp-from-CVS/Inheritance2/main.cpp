class A
{
public:
  int i;
  void f();
};

void A::f()
{
  i=1;
}

class B:public A
{
public:
  int i;
  void f()
  {
	  i++;
	  A::i++;
  }
};

int main()
{
	B b;
	b.i = 0;
	b.B::i++;
	
	b.A::i = 10;
	
	b.f();
	assert(b.i    == 2);
	assert(b.A::i == 11);

	b.A::f();
	assert(b.A::i == 1);
}
