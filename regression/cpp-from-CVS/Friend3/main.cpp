class A {
	friend void inc(A&);
	friend int get(const A& a);
	int i;
};


void inc(A& a){a.i++;}
int get(const A& a) {return a.i;}

A a;

int main()
{
	inc(a);
	assert(get(a)==1);
}
