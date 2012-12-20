struct A
{
	typedef int INT;
};

struct B: A{};

int main()
{
	B::INT i;
}
