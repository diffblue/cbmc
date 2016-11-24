struct A {
	bool operator << (const A&) const {return true;}
	bool func(const A& a)const{ return operator <<(a);}
};

int main()
{
	A a;
	assert(a.func(a)==true);
}
