struct A
{
	static int i;
};

struct B: public A
{
	static int i;
};

int main()
{
	A::i = 0;
	B::i = 1;
	assert(A::i == 0);
	assert(B::i == 1);

	B obj;
	obj.i++;
	assert(B::i == 2);
	obj.A::i++;
	assert(A::i == 1);
	
}
