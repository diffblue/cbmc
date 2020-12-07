#include <stdlib.h>
#include <assert.h>
#include<stdbool.h>

#define MAX_LEN 100

bool main(){
    char * a1;
    char * a2;
    size_t a1_len;
    size_t a2_len;
    size_t i = 0;
    bool res = true;

    __CPROVER_assume(a1_len < MAX_LEN);
    __CPROVER_assume(a2_len < MAX_LEN);
    a1 = malloc(a1_len);
    a2 = malloc(a2_len);
    

    //This should lead to an out of bounds error.
    //Also, tests that our abstraction works for while loops.
    while(i < a1_len){
        if(a1[i] != a2[i]) res &= false;
        i++;
    }
    
    return res;
}