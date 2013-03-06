typedef int INTTYPE;

int func1();

typeof(int) v1;
typeof(INTTYPE) v2;
typeof(v2) v3;
typeof(1+1) v4;
typeof(1+1+func1()) v5;
const typeof(int) v6;
typeof(int) const v7;
static typeof(int) const v8;
static typeof(int) const *v9;
static volatile typeof(int) const *v10;

void func2(typeof(int) *some_arg)
{
}

int main()
{
}
