struct A {
	int i;
	A():i(0){}
	int get_i(){return i;}
};

A factory(){
	return A();
}

int main()
{
	// Altough the returned value of `factory' is an
	// rvalue, gcc accepts to bind it to the `this'
	// parameter of the method `get_i'. Note that when used,
	// a returned value is stored in a temporary
	// (see goto_convertt::remove_function_call). Thus,
	// the value returned by a function call can be treated
	// as an lvalue.
	//
	// It's not clear what the best is. Should this code be rejected?
	// Is the compatibility with gcc more important?
	
	assert(factory().get_i() == 0);
	
}
