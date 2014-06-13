#include "stdlib.h"


typedef enum _dummyEnum{

    first=0,

    second/*=1*/,

    third/*=2*/,
    fourth

} dummyEnum;


int8_t StateMachines_testFlightAnalyzer(void) {

    int8_t __failuresVal = 0;

    dummyEnum __currentState;



    if ( __currentState != fourth ) {

        __failuresVal++;

    }



    return __failuresVal;

}



int main() {}

