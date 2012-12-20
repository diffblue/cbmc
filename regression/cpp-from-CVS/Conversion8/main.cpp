int main() {
	const char c[1] = {'c'};
	char* pc;
	const char** pcc = &pc; //1: not allowed
	*pcc = &c;
	*pc = 'C'; //2: modifies a const object
	assert(c[0]=='c');
}
