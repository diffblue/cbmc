
struct A
{
	int i;
	int func(){return i;}
};

struct B
{
	A* pa;
	int (A::* pmethod)();
        B(A* pa, int (A::* pmethod)()):pa(pa),pmethod(pmethod){}
	int eval(){return (pa->*pmethod)();}	
};

int main()
{
	A a;
	B b(&a, &A::func);
	assert(b.eval() == a.i);
}
