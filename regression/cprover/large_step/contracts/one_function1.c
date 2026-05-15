void my_function1() __CPROVER_ensures(0) // fails
{
}

void my_function2() __CPROVER_ensures(1) // passes
{
}
