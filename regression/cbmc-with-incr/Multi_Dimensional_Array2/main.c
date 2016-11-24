/* case 2 w/o any option */
unsigned int nondet_uint();
int main(){
    int array[3][3]={{0,0,0},{1,1,1},{2,2,2}};

    unsigned int a, b;
    a = nondet_uint();
    b = nondet_uint();
    __CPROVER_assume (a < 3 && b < 3);
    array[a][a] = array[b][b]; // 1st array assign
    array[a][a] = array[b][b]; // 2nd array assign
    assert(array[a][a] >= 0);
}
/* end of case 2 */
