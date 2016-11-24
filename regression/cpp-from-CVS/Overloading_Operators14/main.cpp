struct A
{
	typedef int INT;
	int i;
	operator INT() { return i;}
	INT value(){return operator INT();}
};

int main()
{
	A a;
	a.i = 20;
	assert( a.value() == 20);
}
