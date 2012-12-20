
struct C
{
	int d;
};

struct B
{
	C c;
	C* operator->()
	{
		return &c;
	}
};

struct A
{
	B b;	
	B& operator->()
	{
		return b;
	}
};

int main()
{
	A a;
	a->d = 2;
	assert(a.b.c.d==2);
}
