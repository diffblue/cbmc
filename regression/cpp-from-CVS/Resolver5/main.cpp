namespace n1
{
	struct A {
		int i;
	};

	int func(A a){return a.i;}
}

int main()
{
	n1::A obj1;
	obj1.i = 200;

	assert(func(obj1) == 200); // Argument-dependant name lookup
	
	return 0;
}
