struct A
{
	int i;
	A(){};
	protected:
	A(int i):i(i){};
	
};

struct B: A
{
	B():A(0){}	
};

B b;

int main()
{
	assert(b.i==0);
}
