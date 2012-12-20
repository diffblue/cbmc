template<class T> class Y {
public:
       void f() {
           T::A++;   // T::A is not a type name!
	}
};

class B
{
	public:
	static int A;
};

int B::A = 0;
int main(){
	Y<B> y;
	y.f();
	assert(B::A == 1);
}
