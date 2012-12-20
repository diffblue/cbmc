struct A {
	typedef int INT;
};

struct B: public A
{
	INT i;
	void set(INT i)
	{
		this->i = i;
	}
};

int main()
{
	B b;
	b.i = 0;
	b.i++;
	assert(b.i==1);
}
