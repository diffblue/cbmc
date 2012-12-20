// tag only, but with default parameter
template<typename T1, typename T2=int>
class my_template1;

// body, but without default parameter
template<typename T1, typename T2>
class my_template1
{
};

// should work!
my_template1<char> some_instance1;

// tag only, no default parameter
template<typename T1, typename T2>
class my_template2;

// body, but without default parameter
template<typename T1, typename T2=int>
class my_template2
{
};

// should work!
my_template2<char> some_instance2;
