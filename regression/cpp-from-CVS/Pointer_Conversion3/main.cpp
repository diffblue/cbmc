struct A {
	int i;
	
};

struct B
{
	int j;
	int k;
};

int main()
{
	A* pa;
	B* pb;
	pb = static_cast<B*>(pa);  // ill-formed
}
