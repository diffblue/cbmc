struct A{
        int x;
	A(){}
};

struct B: public A{
	B(){}
};

int main()
{
	B b1,b2;
	b1 = b2;
	assert(b1.x == b2.x);
}
