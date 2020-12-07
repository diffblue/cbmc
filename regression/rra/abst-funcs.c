#include <stdint.h>
#include <assert.h>
#include <stddef.h>
#include <stdbool.h>

//Some helper functions. 

//nndt_bool, nndt_int, nndt_sizet are available in CBMC.

size_t nndt_int(){
    size_t i;
    return(i);
}

bool nndt_bool(){
    size_t i;
    return(i % 2);
}


size_t nndt_under(size_t bound){
    size_t nd;
    // Mod is an expensive operation. We need to get rid of this.
    //return(nd%bound);
    __CPROVER_assume(nd < bound);
    return(nd);
}

size_t nndt_between(size_t l, size_t u){
    size_t diff = u - l;
    size_t nd = nndt_under(diff);
    if (nd == 0) return(l+1);
    else return(nd + l);
}

size_t nndt_above(size_t bound){
    size_t nd = nndt_int();
    __CPROVER_assume(nd < bound);
    return(nd);
}

//For one index: *c*
// covers c*, +c*
size_t one_abs(size_t index, size_t a1){
    if(index < a1) return(0);
    else if(index == a1) return(1);
    else return(2);
}


bool is_precise_1(size_t abs_ind, size_t a1){
    return(abs_ind == 1);
}

bool is_abstract_1(size_t abs_ind, size_t a1){
    return(abs_ind != 1);
}

size_t concretize_1(size_t abs_ind, size_t a1){
    assert(abs_ind >= 0);
    assert(a1 >= 0);
    if(abs_ind < 1) {
        if (a1 == 0) 
        {
            assert(0);
            return(0);
        }
        else return(nndt_under(a1));
    }
    else if (abs_ind == 1) return(a1);
    else return(nndt_above(a1));
}

// Add a number to an abs_ind
size_t add_abs_to_conc_1(size_t abs_ind, size_t num, size_t a1){
    if (num == 1){
        if(abs_ind == 0) {
            if (nndt_bool() > 0) return(abs_ind);
            else return(abs_ind + 1);
        }
        //abs_ind = 1 or 2
        else return(2);
    }
    else {
        assert(num >= 2);
        //This might be inefficient model checking wise.
        //We can always write an explicit abstraction like we did for num = 1.
        size_t conc = concretize_1(abs_ind, a1);
        return(one_abs(conc+num, a1));
    }

}

size_t sub_conc_from_abs_1(size_t abs_ind, size_t num, size_t a1){
    if (num == 1){
        if(abs_ind == 2) {
            if (nndt_bool() > 0) return(abs_ind);
            else return(abs_ind - 1);
        }
        //abs_ind = 1 0r 0
        else return(0);
    }
    else {
        assert(num >= 2);
        //This might be inefficient model checking wise.
        //We can always write an explicit abstraction like we did for num = 1.
        size_t conc = concretize_1(abs_ind, a1);
        assert(conc>=num);
        return(one_abs(conc-num, a1));
    }
}



// For two indices

//Get the abstraction of an index for shape *c*c*.
//Cases +c+c*, c+c*, +cc*, c+c*, cc+ can all be 
//handled by the same function as long as we are careful with concretization, increment and other funcs.
//If model checking time is affected then we can split into finer cases.
size_t two_abs(size_t index, size_t a1, size_t a2) {
    if (a1==0 && a1+1==a2) {  // cc*
        if (index == a1) return 0;
        else if (index == a2) return 1;
        else return 2;
    } else if (!(a1==0) && a1+1==a2) {  // *cc*
        if (index < a1) return 0;
        else if (index == a1) return 1;
        else if (index == a2) return 2;
        else return 3;
    } else if (a1==0 && !(a1+1==a2)) {  // c*c*
        if (index == a1) return 0;
        else if (index > a1 && index < a2) return 1;
        else if (index == a2) return 2;
        else return 3;
    } else {  // *c*c*, !a1==0 && !a1+1==a2
        if (index < a1) return 0;
        else if (index == a1) return 1;
        else if (index > a1 && index < a2) return 2;
        else if (index == a2) return 3;
        else return 4;
    }
}


//Get the concretization of an index. We assume all args are >= 0
//Shape *c*c*
size_t concretize_2(size_t abs_ind, size_t a1, size_t a2) {
    assert(abs_ind >= 0);
    assert(a1 >= 0);
    assert(a2 > a1);

    if (a1==0 && a1+1==a2) {  // cc*
        if (abs_ind == 0) return a1;
        else if (abs_ind == 1) return a2;
        else if (abs_ind == 2) return nndt_above(a2);
        else {
            assert(0!=0);
            return 0;
        }
    } else if (!(a1==0) && a1+1==a2) {  // *cc*
        if (abs_ind == 0) return nndt_under(a1);
        else if (abs_ind == 1) return a1;
        else if (abs_ind == 2) return a2;
        else if (abs_ind == 3) return nndt_above(a2);
        else {
            assert(0!=0);
            return 0;
        }
    } else if (a1==0 && !(a1+1==a2)) {  // c*c*
        if (abs_ind == 0) return a1;
        else if (abs_ind == 1) return nndt_between(a1, a2);
        else if (abs_ind == 2) return a2;
        else if (abs_ind == 3) return nndt_above(a2);
        else {
            assert(0!=0);
            return 0;
        }
    } else {  // *c*c*, !a1==0 && !a1+1==a2
        if (abs_ind == 0) return nndt_under(a1);
        else if (abs_ind == 1) return a1;
        else if (abs_ind == 2) return nndt_between(a1, a2);
        else if (abs_ind == 3) return a2;
        else if (abs_ind == 4) return nndt_above(a2);
        else {
            assert(0!=0);
            return 0;
        }
    }
}

int is_precise_2(size_t abs_ind, size_t a1, size_t a2){
    if (a1==0 && a1+1==a2) {  // cc*
        return abs_ind == 0 || abs_ind == 1;
    } else if (!(a1==0) && a1+1==a2) {  // *cc*
        return abs_ind == 1 || abs_ind == 2;
    } else if (a1==0 && !(a1+1==a2)) {  // c*c*
        return abs_ind == 0 || abs_ind == 2;
    } else {  // *c*c*, !a1==0 && !a1+1==a2
        return abs_ind == 1 || abs_ind == 3;
    }
}

int is_abstract_2(size_t abs_ind, size_t a1, size_t a2){
    int pre = is_precise_2(abs_ind, a1, a2);
    return(1-pre);
}

// Add a number to an abs_ind
size_t add_abs_to_conc_2(size_t abs_ind, size_t num, size_t a1, size_t a2){
    // if (num == 0){
    //     return abs_ind;
    // }
    // else if (num == 1){
    //     if(abs_ind == 0 || abs_ind == 2) {
    //         if (nndt_bool() > 0) return(abs_ind);
    //         else return(abs_ind + 1);
    //     }
    //     else if (abs_ind == 1) {
    //         // case *cc*
    //         if (a2 == a1+1) return(3);
    //         else return(2);
    //     }
    //     //abs_ind = 3 or 4
    //     else return(4);
    // }
    // else {
    //     assert(num >= 2);
    //     //This might be inefficient model checking wise.
    //     //We can always write an explicit abstraction like we did for num = 1.
    //     int conc = concretize_2(abs_ind, a1, a2);
    //     return(two_abs(conc+num, a1, a2));
    // }
    size_t conc = concretize_2(abs_ind, a1, a2);
    return two_abs(conc+num, a1, a2);

}

size_t sub_conc_from_abs_2(size_t abs_ind, size_t num, size_t a1, size_t a2){
    // if (num == 1){
    //     if(abs_ind == 4 || abs_ind == 2) {
    //         if (nndt_bool() > 0) return(abs_ind);
    //         else return(abs_ind - 1);
    //     }
    //     else if (abs_ind == 3) {
    //         if (a1 == a2) return(1);
    //         else return(2);
    //     }
    //     //abs_ind = 1 0r 0
    //     else return(0);
    // }
    // else {
    //     assert(num >= 2);
    //     //This might be extremely inefficient model checking wise.
    //     //We can always write an explicit abstraction like we did for num = 1.
    //     int conc = concretize_2(abs_ind, a1, a2);
    //     return(two_abs(conc-num, a1, a2));
    // }
    size_t conc = concretize_2(abs_ind, a1, a2);
    assert(conc >= num);
    return two_abs(conc-num, a1, a2);
}

// helper function
// translate an index from *c*c*c* to the real one depending on value of a1, a2, a3
// e.g. when a1=0, a1+1==a2, *c*c*c* becomes cc*c*
// index 4 in *c*c*c* will be translated into 2 by this function
size_t raw_to_real_3(size_t raw_index, size_t a1, size_t a2, size_t a3)
{
  return raw_index - (raw_index >= 1 && a1 == 0) -
         (raw_index >= 3 && a1 + 1 == a2) - (raw_index >= 5 && a2 + 1 == a3);
}

// helper function, the reversed version of raw_to_real
// *c*c*c*
// c1: 1-(a1==0)
// c2: 3-(a1==0)-(a1+1==a2)
// c3: 5-(a1==0)-(a1+1==a2)-(a2+1==a3)
size_t real_to_raw_3(size_t real_index, size_t a1, size_t a2, size_t a3)
{
    if (real_index < 1-(a1==0))
        return 0;
    else if (real_index == 1-(a1==0))
        return 1;
    else if (real_index < 3-(a1==0)-(a1+1==a2))
        return 2;
    else if (real_index == 3-(a1==0)-(a1+1==a2))
        return 3;
    else if (real_index < 5-(a1==0)-(a1+1==a2)-(a2+1==a3))
        return 4;
    else if (real_index == 5-(a1==0)-(a1+1==a2)-(a2+1==a3))
        return 5;
    else
        return 6;
}

// Three indices: *c*c*c*
// *1: exist if a1>0
// *2: exist if a1+1!=a2
// *3: exist if a2+1!=a3
size_t three_abs(size_t index, size_t a1, size_t a2, size_t a3) {
    size_t raw_index = 0;
    if (index < a1) raw_index = 0;
    else if (index == a1) raw_index = 1;
    else if (index > a1 && index < a2) raw_index = 2;
    else if (index == a2) raw_index = 3;
    else if (index > a2 && index < a3) raw_index = 4;
    else if (index == a3) raw_index = 5;
    else raw_index = 6;
    return raw_to_real_3(raw_index, a1, a2, a3);
}

// Three indices: *c*c*c*
// Return the concrete index corresponding to abs_ind
size_t concretize_3(size_t abs_ind, size_t a1, size_t a2, size_t a3)
{
    size_t raw_index = real_to_raw_3(abs_ind, a1, a2, a3);
    if (raw_index == 0)
        return nndt_under(a1);
    else if (raw_index == 1)
        return a1;
    else if (raw_index == 2)
        return nndt_between(a1, a2);
    else if (raw_index == 3)
        return a2;
    else if (raw_index == 4)
        return nndt_between(a2, a3);
    else if (raw_index == 5)
        return a3;
    else
        return nndt_above(a3);
}

int is_precise_3(size_t abs_ind, size_t a1, size_t a2, size_t a3){
    size_t raw_ind = real_to_raw_3(abs_ind, a1, a2, a3);
    return (raw_ind == 1) || (raw_ind == 3) || (raw_ind == 5);
}

// Add a number to an abs_ind
size_t add_abs_to_conc_3(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3){
    if (num == 0) {
        return abs_ind;
    } else if (num == 1) {
        if (is_precise_3(abs_ind, a1, a2, a3)) {
            return abs_ind + 1;
        } else {
            return (abs_ind > 5-(a1==0)-(a1+1==a2)-(a2+1==a3) || nndt_bool()) ? abs_ind: abs_ind + 1;
        }
    } else {
        size_t conc = concretize_3(abs_ind, a1, a2, a3);
        return three_abs(conc+num, a1, a2, a3);
    }
}

size_t sub_conc_from_abs_3(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3){
    if (num == 0) {
        return abs_ind;
    } else if (num == 1) {
        if (is_precise_3(abs_ind, a1, a2, a3)) {
            if (abs_ind != 0)
                return abs_ind - 1;
            else
                assert(0 != 0);  // this is to cover the overflow case 0-1
        } else {
            return (abs_ind == 0 || nndt_bool()) ? abs_ind: abs_ind - 1;
        }
    } else {
        size_t conc = concretize_3(abs_ind, a1, a2, a3);
        assert(conc >= num);
        return three_abs(conc-num, a1, a2, a3);
    }
}

size_t multiply_abs_with_conc_3(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3) {
    if (num == 0) {
        return 0;
    } else if (num == 1) {
        return abs_ind;
    } else {
        size_t conc = concretize_3(abs_ind, a1, a2, a3);
        return three_abs(abs_ind*num, a1, a2, a3);
    }
}

// helper function
// translate an index from *c*c*c*c* to the real one depending on value of a1, a2, a3, a4
// e.g. when a1=0, a1+1==a2, *c*c*c*c* becomes cc*c*c*
// index 4 in *c*c*c*c* will be translated into 2 by this function
size_t raw_to_real_4(size_t raw_index, size_t a1, size_t a2, size_t a3, size_t a4)
{
  return raw_index - (raw_index >= 1 && a1 == 0) -
         (raw_index >= 3 && a1 + 1 == a2) - (raw_index >= 5 && a2 + 1 == a3) -
         (raw_index >= 7 && a3 + 1 == a4);
}

// helper function, the reversed version of raw_to_real
// *c*c*c*c*
// c1: 1-(a1==0)
// c2: 3-(a1==0)-(a1+1==a2)
// c3: 5-(a1==0)-(a1+1==a2)-(a2+1==a3)
// c4: 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)
size_t real_to_raw_4(size_t real_index, size_t a1, size_t a2, size_t a3, size_t a4)
{
    if (real_index < 1-(a1==0))
        return 0;
    else if (real_index == 1-(a1==0))
        return 1;
    else if (real_index < 3-(a1==0)-(a1+1==a2))
        return 2;
    else if (real_index == 3-(a1==0)-(a1+1==a2))
        return 3;
    else if (real_index < 5-(a1==0)-(a1+1==a2)-(a2+1==a3))
        return 4;
    else if (real_index == 5-(a1==0)-(a1+1==a2)-(a2+1==a3))
        return 5;
    else if (real_index < 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4))
        return 6;
    else if (real_index == 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4))
        return 7;
    else
        return 8;
}

//Get the abstraction of an index for shape *c*c*c*c*.
//If model checking time is affected then we can split into finer cases.
size_t four_abs(size_t index, size_t a1, size_t a2, size_t a3, size_t a4) {
    size_t raw_index = 0;
    if (index < a1) raw_index = 0;
    else if (index == a1) raw_index = 1;
    else if (index > a1 && index < a2) raw_index = 2;
    else if (index == a2) raw_index = 3;
    else if (index > a2 && index < a3) raw_index = 4;
    else if (index == a3) raw_index = 5;
    else if (index > a3 && index < a4) raw_index = 6;
    else if (index == a4) raw_index = 7;
    else raw_index = 8;
    return raw_to_real_4(raw_index, a1, a2, a3, a4);
}

//Get the concretization of an index. We assume all args are >= 0
//Shape *c*c*c*c*
size_t concretize_4(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4) {
    assert(a1<a2);
    assert(a2<a3);
    assert(a3<a4);
    size_t raw_index = real_to_raw_4(abs_ind, a1, a2, a3, a4);
    if (raw_index == 0)
        return nndt_under(a1);
    else if (raw_index == 1)
        return a1;
    else if (raw_index == 2)
        return nndt_between(a1, a2);
    else if (raw_index == 3)
        return a2;
    else if (raw_index == 4)
        return nndt_between(a2, a3);
    else if (raw_index == 5)
        return a3;
    else if (raw_index == 6)
        return nndt_between(a3, a4);
    else if (raw_index == 7)
        return a4;
    else
        return nndt_above(a4);
}

int is_precise_4(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4){
    size_t raw_ind = real_to_raw_4(abs_ind, a1, a2, a3, a4);
    return (raw_ind == 1 || raw_ind == 3 || raw_ind == 5 || raw_ind == 7);
}

int is_abstract_4(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4){
    return !is_precise_4(abs_ind, a1, a2, a3, a4);
}

// Add a number to an abs_ind
size_t add_abs_to_conc_4(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4){
    if (num == 0) {
        return abs_ind;
    } else if (num == 1) {
        if (is_precise_4(abs_ind, a1, a2, a3, a4)) {
            return abs_ind + 1;
        } else {
            return (abs_ind > 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4) || nndt_bool()) ? abs_ind: abs_ind + 1;
        }
    } else {
        size_t conc = concretize_4(abs_ind, a1, a2, a3, a4);
        return four_abs(conc+num, a1, a2, a3, a4);
    }

}
// Substract a number from abs_ind
size_t sub_conc_from_abs_4(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4){
    if (num == 0) {
        return abs_ind;
    } else if (num == 1) {
        if (is_precise_4(abs_ind, a1, a2, a3, a4)) {
            if (abs_ind != 0)
                return abs_ind - 1;
            else
                assert(0 != 0);  // this is to cover the overflow case 0-1
        } else {
            return (abs_ind == 0 || nndt_bool()) ? abs_ind: abs_ind - 1;
        }
    } else {
        size_t conc = concretize_4(abs_ind, a1, a2, a3, a4);
        assert(conc >= num);
        return four_abs(conc-num, a1, a2, a3, a4);
    }
}

size_t multiply_abs_with_conc_4(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4) {
    if (num == 0) {
        return 0;
    } else if (num == 1) {
        return abs_ind;
    } else {
        size_t conc = concretize_4(abs_ind, a1, a2, a3, a4);
        return four_abs(abs_ind*num, a1, a2, a3, a4);
    }
}

// helper function
// translate an index from *c*c*c*c*c* to the real one depending on value of a1, a2, a3, a4, a5
// e.g. when a1=0, a1+1==a2, *c*c*c*c*c* becomes cc*c*c*c*
// index 4 in *c*c*c*c*c* will be translated into 2 by this function
size_t raw_to_real_5(size_t raw_index, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5)
{
  return raw_index - (raw_index >= 1 && a1 == 0) -
         (raw_index >= 3 && a1 + 1 == a2) - (raw_index >= 5 && a2 + 1 == a3) -
         (raw_index >= 7 && a3 + 1 == a4) - (raw_index >= 9 && a4 + 1 == a5);
}

// helper function, the reversed version of raw_to_real
// *c*c*c*c*c*
// c1: 1-(a1==0)
// c2: 3-(a1==0)-(a1+1==a2)
// c3: 5-(a1==0)-(a1+1==a2)-(a2+1==a3)
// c4: 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)
// c5: 9-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5)
size_t real_to_raw_5(size_t real_index, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5)
{
    if (real_index < 1-(a1==0))
        return 0;
    else if (real_index == 1-(a1==0))
        return 1;
    else if (real_index < 3-(a1==0)-(a1+1==a2))
        return 2;
    else if (real_index == 3-(a1==0)-(a1+1==a2))
        return 3;
    else if (real_index < 5-(a1==0)-(a1+1==a2)-(a2+1==a3))
        return 4;
    else if (real_index == 5-(a1==0)-(a1+1==a2)-(a2+1==a3))
        return 5;
    else if (real_index < 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4))
        return 6;
    else if (real_index == 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4))
        return 7;
    else if (real_index < 9-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5))
        return 8;
    else if (real_index == 9-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5))
        return 9;
    else
        return 10;
}

//Get the abstraction of an index for shape *c*c*c*c*.
//If model checking time is affected then we can split into finer cases.
size_t five_abs(size_t index, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5) {
    size_t raw_index = 0;
    if (index < a1) raw_index = 0;
    else if (index == a1) raw_index = 1;
    else if (index > a1 && index < a2) raw_index = 2;
    else if (index == a2) raw_index = 3;
    else if (index > a2 && index < a3) raw_index = 4;
    else if (index == a3) raw_index = 5;
    else if (index > a3 && index < a4) raw_index = 6;
    else if (index == a4) raw_index = 7;
    else if (index > a4 && index < a5) raw_index = 8;
    else if (index == a5) raw_index = 9;
    else raw_index = 10;
    return raw_to_real_5(raw_index, a1, a2, a3, a4, a5);
}

//Get the concretization of an index. We assume all args are >= 0
//Shape *c*c*c*c*c*
size_t concretize_5(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5) {
    assert(a1<a2);
    assert(a2<a3);
    assert(a3<a4);
    assert(a4<a5);
    size_t raw_index = real_to_raw_5(abs_ind, a1, a2, a3, a4, a5);
    if (raw_index == 0)
        return nndt_under(a1);
    else if (raw_index == 1)
        return a1;
    else if (raw_index == 2)
        return nndt_between(a1, a2);
    else if (raw_index == 3)
        return a2;
    else if (raw_index == 4)
        return nndt_between(a2, a3);
    else if (raw_index == 5)
        return a3;
    else if (raw_index == 6)
        return nndt_between(a3, a4);
    else if (raw_index == 7)
        return a4;
    else if (raw_index == 8)
        return nndt_between(a4, a5);
    else if (raw_index == 9)
        return a5;
    else
        return nndt_above(a5);
}

int is_precise_5(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5){
    size_t raw_ind = real_to_raw_5(abs_ind, a1, a2, a3, a4, a5);
    return (raw_ind == 1 || raw_ind == 3 || raw_ind == 5 || raw_ind == 7 || raw_ind == 9);
}

int is_abstract_5(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5){
    return !is_precise_5(abs_ind, a1, a2, a3, a4, a5);
}

// Add a number to an abs_ind
size_t add_abs_to_conc_5(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5){
    if (num == 0) {
        return abs_ind;
    } else if (num == 1) {
        if (is_precise_5(abs_ind, a1, a2, a3, a4, a5)) {
            return abs_ind + 1;
        } else {
            return (abs_ind > 9-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5) || nndt_bool()) ? abs_ind: abs_ind + 1;
        }
    } else {
        size_t conc = concretize_5(abs_ind, a1, a2, a3, a4, a5);
        return five_abs(conc+num, a1, a2, a3, a4, a5);
    }

}
// Substract a number from abs_ind
size_t sub_conc_from_abs_5(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5){
    if (num == 0) {
        return abs_ind;
    } else if (num == 1) {
        if (is_precise_5(abs_ind, a1, a2, a3, a4, a5)) {
            if (abs_ind != 0)
                return abs_ind - 1;
            else
                assert(0 != 0);  // this is to cover the overflow case 0-1
        } else {
            return (abs_ind == 0 || nndt_bool()) ? abs_ind: abs_ind - 1;
        }
    } else {
        size_t conc = concretize_5(abs_ind, a1, a2, a3, a4, a5);
        assert(conc >= num);
        return five_abs(conc-num, a1, a2, a3, a4, a5);
    }
}

size_t multiply_abs_with_conc_5(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5) {
    if (num == 0) {
        return 0;
    } else if (num == 1) {
        return abs_ind;
    } else {
        size_t conc = concretize_5(abs_ind, a1, a2, a3, a4, a5);
        return five_abs(abs_ind*num, a1, a2, a3, a4, a5);
    }
}

// helper function
// translate an index from *c*c*c*c*c*c* to the real one depending on value of a1, a2, a3, a4, a5, a6
// e.g. when a1=0, a1+1==a2, *c*c*c*c*c*c* becomes cc*c*c*c*c*
// index 4 in *c*c*c*c*c*c* will be translated into 2 by this function
size_t raw_to_real_6(size_t raw_index, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6)
{
  return raw_index - (raw_index >= 1 && a1 == 0) -
         (raw_index >= 3 && a1 + 1 == a2) - (raw_index >= 5 && a2 + 1 == a3) -
         (raw_index >= 7 && a3 + 1 == a4) - (raw_index >= 9 && a4 + 1 == a5) - 
         (raw_index >= 11 && a5 + 1 == a6);
}

// helper function, the reversed version of raw_to_real
// *c*c*c*c*c*c*
// c1: 1-(a1==0)
// c2: 3-(a1==0)-(a1+1==a2)
// c3: 5-(a1==0)-(a1+1==a2)-(a2+1==a3)
// c4: 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)
// c5: 9-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5)
// c6: 11-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5)-(a5+1==a6)
size_t real_to_raw_6(size_t real_index, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6)
{
    if (real_index < 1-(a1==0))
        return 0;
    else if (real_index == 1-(a1==0))
        return 1;
    else if (real_index < 3-(a1==0)-(a1+1==a2))
        return 2;
    else if (real_index == 3-(a1==0)-(a1+1==a2))
        return 3;
    else if (real_index < 5-(a1==0)-(a1+1==a2)-(a2+1==a3))
        return 4;
    else if (real_index == 5-(a1==0)-(a1+1==a2)-(a2+1==a3))
        return 5;
    else if (real_index < 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4))
        return 6;
    else if (real_index == 7-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4))
        return 7;
    else if (real_index < 9-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5))
        return 8;
    else if (real_index == 9-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5))
        return 9;
    else if (real_index < 11-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5)-(a5+1==a6))
        return 10;
    else if (real_index == 11-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5)-(a5+1==a6))
        return 11;
    else
        return 12;
}

//Get the abstraction of an index for shape *c*c*c*c*c*.
//If model checking time is affected then we can split into finer cases.
size_t six_abs(size_t index, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6) {
    size_t raw_index = 0;
    if (index < a1) raw_index = 0;
    else if (index == a1) raw_index = 1;
    else if (index > a1 && index < a2) raw_index = 2;
    else if (index == a2) raw_index = 3;
    else if (index > a2 && index < a3) raw_index = 4;
    else if (index == a3) raw_index = 5;
    else if (index > a3 && index < a4) raw_index = 6;
    else if (index == a4) raw_index = 7;
    else if (index > a4 && index < a5) raw_index = 8;
    else if (index == a5) raw_index = 9;
    else if (index > a5 && index < a6) raw_index = 10;
    else if (index == a6) raw_index = 11;
    else raw_index = 12;
    return raw_to_real_6(raw_index, a1, a2, a3, a4, a5, a6);
}

//Get the concretization of an index. We assume all args are >= 0
//Shape *c*c*c*c*c*c*
size_t concretize_6(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6) {
    assert(a1<a2);
    assert(a2<a3);
    assert(a3<a4);
    assert(a4<a5);
    assert(a5<a6);
    size_t raw_index = real_to_raw_6(abs_ind, a1, a2, a3, a4, a5, a6);
    if (raw_index == 0)
        return nndt_under(a1);
    else if (raw_index == 1)
        return a1;
    else if (raw_index == 2)
        return nndt_between(a1, a2);
    else if (raw_index == 3)
        return a2;
    else if (raw_index == 4)
        return nndt_between(a2, a3);
    else if (raw_index == 5)
        return a3;
    else if (raw_index == 6)
        return nndt_between(a3, a4);
    else if (raw_index == 7)
        return a4;
    else if (raw_index == 8)
        return nndt_between(a4, a5);
    else if (raw_index == 9)
        return a5;
    else if (raw_index == 10)
        return nndt_between(a5, a6);
    else if (raw_index == 11)
        return a6;
    else
        return nndt_above(a6);
}

int is_precise_6(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6){
    size_t raw_ind = real_to_raw_6(abs_ind, a1, a2, a3, a4, a5, a6);
    return (raw_ind == 1 || raw_ind == 3 || raw_ind == 5 || raw_ind == 7 || raw_ind == 9 || raw_ind == 11);
}

int is_abstract_6(size_t abs_ind, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6){
    return !is_precise_6(abs_ind, a1, a2, a3, a4, a5, a6);
}

// Add a number to an abs_ind
size_t add_abs_to_conc_6(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6){
    if (num == 0) {
        return abs_ind;
    } else if (num == 1) {
        if (is_precise_6(abs_ind, a1, a2, a3, a4, a5, a6)) {
            return abs_ind + 1;
        } else {
            return (abs_ind > 11-(a1==0)-(a1+1==a2)-(a2+1==a3)-(a3+1==a4)-(a4+1==a5)-(a5+1==a6) || nndt_bool()) ? abs_ind: abs_ind + 1;
        }
    } else {
        size_t conc = concretize_6(abs_ind, a1, a2, a3, a4, a5, a6);
        return six_abs(conc+num, a1, a2, a3, a4, a5, a6);
    }

}
// Substract a number from abs_ind
size_t sub_conc_from_abs_6(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6){
    if (num == 0) {
        return abs_ind;
    } else if (num == 1) {
        if (is_precise_6(abs_ind, a1, a2, a3, a4, a5, a6)) {
            if (abs_ind != 0)
                return abs_ind - 1;
            else
                assert(0 != 0);  // this is to cover the overflow case 0-1
        } else {
            return (abs_ind == 0 || nndt_bool()) ? abs_ind: abs_ind - 1;
        }
    } else {
        size_t conc = concretize_6(abs_ind, a1, a2, a3, a4, a5, a6);
        assert(conc >= num);
        return six_abs(conc-num, a1, a2, a3, a4, a5, a6);
    }
}

size_t multiply_abs_with_conc_6(size_t abs_ind, size_t num, size_t a1, size_t a2, size_t a3, size_t a4, size_t a5, size_t a6) {
    if (num == 0) {
        return 0;
    } else if (num == 1) {
        return abs_ind;
    } else {
        size_t conc = concretize_6(abs_ind, a1, a2, a3, a4, a5, a6);
        return six_abs(abs_ind*num, a1, a2, a3, a4, a5, a6);
    }
}
