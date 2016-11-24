struct A { int i;};
struct B: A { char j;};
int main()
{
	A a;
	const A& ra = a;
	static_cast<B&>(ra); //not ok
}
