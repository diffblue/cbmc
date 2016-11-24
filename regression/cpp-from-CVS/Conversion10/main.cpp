struct A {};

struct B {
	 explicit B(A&){}	
};

void test(const B& b){};

int main()
{
	A a;
	test(a); // conversion error
}
