struct B
{
	int j;
	B(int j):j(j){}
};

struct A
{
	int i;
	A(int i): i(i){}
	A(const B& b):i(b.j){}
};

struct C: public A
{
	C(int i): A(i){}
};


int func1(const A& a)
{
	return a.i;
}

int func2(A& a)
{
	return a.i;
}

int func3(A a)
{
	return a.i;
}

int main()
{
	A a1(10);
	assert(func1(a1)==10);
	assert(func2(a1)==10);
	assert(func3(a1)==10);

	const A a2(20);
	assert(func1(a2)==20);
	assert(func3(a2)==20);

	A& r1 = a1;
	assert(func1(r1)==10);
	assert(func2(r1)==10);
	assert(func3(r1)==10);

	const A& r2 = a1;
	assert(func1(r2)==10);
	assert(func3(r2)==10);

	B b1(30);
	assert(func3(b1)==30);

	B& r3 = b1;
	assert(func3(r3)==30);

	const B& r4 = b1;
	assert(func3(r4)==30);

	C c1(40);
	assert(func1(c1)==40);
	assert(func2(c1)==40);
	assert(func3(c1)==40);

	const C c2(50);
	assert(func1(c2)==50);
	assert(func3(c2)==50);

	C& r5 = c1;
	assert(func1(r5)==40);
	assert(func2(r5)==40);
	assert(func3(r5)==40);

	const C&  r6 = c2;
	assert(func1(r6)==50);
	assert(func3(r6)==50);
	
}
