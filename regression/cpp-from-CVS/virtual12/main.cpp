struct A {
	virtual int func(){return 1;}
};

struct B: A {
	int func(){return 2;}
};

int call_func1(A a){return a.func();}
int call_func2(A& a){return a.func();}

int main()
{
	B b;
	assert(call_func1(b)==1);
	assert(call_func2(b)==2);
}
