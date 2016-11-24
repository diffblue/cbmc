bool func(){return true;}

bool func(int i)
{
	if(i==0)
		return false;
	return func();
}

int main()
{
	assert(func(1));
}


