typedef void (*func1)(int asd[]);
typedef void (*func2)(int asd);
typedef void (*func3)(int);
typedef void (*func4)(int ...);
typedef void (*func4)(int, ...); // same, how mean!
typedef void func5(int);
typedef void (func5)(int); // same

int main()
{
}
