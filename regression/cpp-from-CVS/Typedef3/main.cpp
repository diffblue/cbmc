
struct B
{
	typedef struct { typedef int INT; } A;
};

int main()
{
	B::A::INT i = 1;
	assert(i == 1);
}
