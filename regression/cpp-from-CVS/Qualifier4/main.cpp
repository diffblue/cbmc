struct A
{
	int f();
};

int main()
{
	int i = (int) A::f;
}
