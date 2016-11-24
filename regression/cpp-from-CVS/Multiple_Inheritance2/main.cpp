struct A{
	int i;
	A(){};
};
struct B: virtual A{};
struct C: virtual A{};
struct D: B, C {};

int main()
{
	D d;
	d.i = 10;
	assert(d.i == 10);
}

