#include <assert.h>
#include <stdio.h>

class base
{
public:
    virtual ~base() {}
    virtual int func(void)
    {
        printf ("In base, returning 1");
        return 1;
    }
};

class derived : public base
{
public:
    virtual ~derived() {}
    virtual int func(void)
    {
        printf ("In derived, returning 2");
        return 2;
    }
};

int main (void)
{
    base* D = new derived;
    int a = D->func();
    delete D;
    assert(a == 2);
    return a;
}


/*
CBMC Error
C:\FormalMethods\CBMC5_1>cbmc.exe C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp
CBMC version 5.1 32-bit i386 windows
Parsing C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp
inheritance_1.cpp
Converting
Type-checking inheritance_1
Generating GOTO Program
Adding CPROVER library
tmp.stdin45548.KyVaaa.c
file <built-in-additions> line 9 function __CPROVER_size_t: syntax error before `__CPROVER_zero_string_length'
Function Pointer Removal
Partial Inlining
Generic Property Instrumentation
Starting Bounded Model Checking
**** WARNING: no body for function __new
**** WARNING: no body for function __delete
size of program expression: 125 steps
simple slicing removed 6 assignments
Generated 1 VCC(s), 1 remaining after simplification
Passing problem to propositional reduction
converting SSA
Running propositional reduction
Post-processing
Solving with MiniSAT 2.2.0 with simplifier
1044 variables, 879 clauses
SAT checker: negated claim is SATISFIABLE, i.e., does not hold
Runtime decision procedure: 0.004s
Building error trace

Counterexample:

State 19 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 26 function main thread 0
----------------------------------------------------
  D=((class *)NULL) (00000000000000000000000000000000)

State 27 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 26 function main thread 0
----------------------------------------------------
  this=((class *)NULL) (00000000000000000000000000000000)

State 28 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 26 function main thread 0
----------------------------------------------------
  this=((class *)NULL) (00000000000000000000000000000000)

State 30  thread 0
----------------------------------------------------
  this=((class *)NULL) (00000000000000000000000000000000)

State 31  thread 0
----------------------------------------------------
  this=((class *)NULL) (00000000000000000000000000000000)

State 32  thread 0
----------------------------------------------------
  this$object.base@vtable_pointer=&tag.base@tag.base.@dtor (00001000000000000000000000000000)

State 34  thread 0
----------------------------------------------------
  this$object.base@vtable_pointer=&tag.base@tag.derived.@dtor (00001001000000000000000000000000)

State 35  thread 0
----------------------------------------------------
  this$object.derived@vtable_pointer=&tag.derived@tag.derived.@dtor (00001010000000000000000000000000)

State 37 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 26 function main thread 0
----------------------------------------------------
  D=((class *)NULL) (00000000000000000000000000000000)

State 38 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 27 function main thread 0
----------------------------------------------------
  a=0 (00000000000000000000000000000000)

State 41 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 27 function main thread 0
----------------------------------------------------
  this=((class *)NULL) (00000000000000000000000000000000)

State 42 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 27 function main thread 0
----------------------------------------------------
  this=((class *)NULL) (00000000000000000000000000000000)
In base, returning 1

State 44 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 9 function func thread 0
----------------------------------------------------
  a=1 (00000000000000000000000000000001)

State 48 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 28 function main thread 0
----------------------------------------------------
  this=((class *)NULL) (00000000000000000000000000000000)

State 49 file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 28 function main thread 0
----------------------------------------------------
  this=((class *)NULL) (00000000000000000000000000000000)

State 50  thread 0
----------------------------------------------------
  this$object.base@vtable_pointer=&tag.base@tag.base.@dtor (00001000000000000000000000000000)

Violated property:
  file C:\FormalMethods\Projects\CPP_Tests\inheritance_1.cpp line 29 function main
  Property 1
  a == 2

VERIFICATION FAILED

C:\FormalMethods\CBMC5_1>

*/
