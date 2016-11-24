class B{
  public:
  virtual int f(){ return 0; }
};


void toBr(B& b)
{
	assert(b.f()==0);
}

int main()
{
	B b;
//	assert(b.f()==0);
	toBr(b);
}
