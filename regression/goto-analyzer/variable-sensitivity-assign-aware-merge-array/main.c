int a[10];

int c[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};

void param_test(int array[])
{
    array[1] = 5;
    // TODO: This is marked as "unknown" when running analysis of param_test and global_test. Doesn't seem correct
    // as array[1] is being assigned one line above?
    __CPROVER_assert(array[1]==5,  "array[1]==5");
}

void param_test_val(int array[], int x)
{
    array[1] = x;
    // TODO: This is marked as "unknown" when running analysis of param_test and global_test. Doesn't seem correct
    // as array[1] is being assigned one line above?
    //__CPROVER_assert(array[1]==5,  "array[1]==5");
}

void global_test()
{
    a[2] = 6;
    __CPROVER_assert(a[2]==6,  "a[2]==6");
    c[8] = 15;
    __CPROVER_assert(c[8]==15,  "c[8]==15");
    // TODO: This is marked as "unknown" when running analysis of global_test. CORRECT?
    __CPROVER_assert(c[9]==9,  "c[9]==9");
}

void pass_param()
{
    int b[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    
    __CPROVER_assert(b[0]==0,  "b[0]==0");
    __CPROVER_assert(b[4]==4,  "b[4]==4");
    __CPROVER_assert(b[8]==8,  "b[8]==8");
    // TODO: This is marked as "unknown" when running analysis of pass_param. CORRECT?
    // The theme here is that global array initialisation assertions are marked as "unknown". Why?
    __CPROVER_assert(c[8]==8,  "c[8]==8");
    
    param_test_val(b, 5);

    __CPROVER_assert(b[1]==5,  "b[1]==5");

    __CPROVER_assert(b[0]==0,  "b[0]==0");
    __CPROVER_assert(b[4]==4,  "b[4]==4");
    __CPROVER_assert(b[8]==8,  "b[8]==8");

    __CPROVER_assert(b[1]==1,  "b[1]==1");
    param_test_val(b, 6);
     __CPROVER_assert(b[1]==5,  "b[1]==5");
     __CPROVER_assert(b[0]==0,  "b[0]==0");
}