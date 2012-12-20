struct A {
	int i;
};

A& operator <<(A& a1, A& a2)
{
	a1.i=a2.i;
	a2.i=0;
	return a1;
}

int main()
{
	A a1, a2;
	a2.i = 400;
	A a3(a1 << a2);
	assert(a2.i==0);
	assert(a3.i==a1.i);
	assert(a1.i==400);
}
