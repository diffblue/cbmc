struct A {
};

struct B: A {
};

struct C: B {
};

bool f1(A&){return true;}
bool f1(B&){return false;}

int main()
{
	C c;
	assert(f1(c)==false);
}

