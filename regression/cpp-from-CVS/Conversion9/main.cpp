struct A
{
};

struct B: A {};

int main()
{
	A a = B();
}
