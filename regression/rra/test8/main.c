#include <stdlib.h>
#include <assert.h>

#define MAX_LEN 100

void main(){
    char * a1;
    char * a2;
    size_t a1_len;
    size_t a2_len;
    size_t i = 0;
    size_t sum;

    __CPROVER_assume(a1_len < MAX_LEN);
    __CPROVER_assume(a2_len < MAX_LEN);
    a1 = malloc(a1_len);
    a2 = malloc(a2_len);

    //We are assigning a variable that is not being abstracted --sum.
    while(i < a1_len){
        if(a1[i] == a2[i]) sum = a1[i];
        i++;
    }
    // This assertion is false, should lead to CBMC finding a counter example
    assert(sum < 0); 
    return;
}