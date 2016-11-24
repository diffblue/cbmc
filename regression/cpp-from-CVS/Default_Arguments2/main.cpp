int func(int i = 0){return i;}

int main()
{
	int (*pfunc)(int) = func;
	assert((*pfunc)(10) == 10);
}
