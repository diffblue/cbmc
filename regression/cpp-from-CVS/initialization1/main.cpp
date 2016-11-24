int g1;

class One
{
	public:
	int o;
	One():o(1){}
};

class A
{
	public:
	static One one;
	A() { assert(one.o == 1); }
};

One A::one;

int main()
{
  assert(g1==0);

  A a;
}
