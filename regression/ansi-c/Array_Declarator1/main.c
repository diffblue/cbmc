/*
Background story as per August 27, 2014.

This, and the following Array_DeclaratorN provide some tests regarding
parsing issues with array declarators.

The discovery of the related bug originated with
https://groups.google.com/forum/#!topic/cprover-support/RvNz0t1YQDY

As indicated there, the following parts of the C99 standard are
relevant here:

6.7.3(2) :
Types other than pointer types derived from object or incomplete types
shall not be restrict-qualified.

6.7.5.3(7):
A declaration of a parameter as ``array of type'' shall be adjusted to
``qualified pointer to type'', where the type qualifiers (if any) are
those specified within the [ and ] of the array type derivation. If the
keyword static also appears within the [ and ] of the array type
derivation, then for each call to the function, the value of the
corresponding actual argument shall provide access to the first element
of an array with at least as many elements as specified by the size
expression. 

6.7.5.3(21):
The following are all compatible function prototype declarators.
  double maximum(int n, int m, double a[n][m]);
  double maximum(int n, int m, double a[*][*]);
  double maximum(int n, int m, double a[ ][*]);
  double maximum(int n, int m, double a[ ][m]);
as are:
  void f(double (* restrict a)[5]);
  void f(double a[restrict][5]);
  void f(double a[restrict 3][5]);
  void f(double a[restrict static 3][5]);
(Note that the last declaration also specifies that the argument
corresponding to a in any call to f must be a non-null pointer to the
first of at least three arrays of 5 doubles, which the others do not.)

The comments in the rule for array_abstract_declarator in 
src/ansi-c/parser.y indicate awareness of the standard regarding this
issue, however, it seems that the case where both TOK_STATIC and
attribute_type_qualifier_list (in either order) occur is not covered, 
even though the standard allows this combination.

Further investigation into this issue also revealed that the rules
do not distinguish whether the array declarator occurs as a function
parameter or not. However, different handling of these two cases is
necessary, as witnessed by the test cases in Array_Declarator2-7.

Array_Declarator1 should be parsed successfully, whereas the other
test cases in Array_Declarator2-7 should lead to a parsing error.
Note that currently Array_Declarator6 and Array_Declarator7 are
successful tests, however, for the wrong reason.

*/

// all foo* should be parsed successfully
void foo0(int x[restrict])
{
}

void foo0Prot(int x[restrict]);

void foo1(int x[static 1U])
{
}

void foo1Prot(int x[static 1U]);

void foo2(int x[restrict 2U])
{
}

void foo2Prot(int x[restrict 2U]);

void foo3(int x[restrict static 3U])
{
}

void foo3Prot(int x[restrict static 3U]);

void foo4(int x[static restrict 4U])
{
}

void foo4Prot(int x[static restrict 4U]);

void foo5(int x[volatile restrict static 5U])
{
}

void foo5Prot(int x[volatile restrict static 5U]);

void foo6(int x[static volatile const restrict 6U])
{
}

void foo6Prot(int x[static volatile const restrict 6U]);

void foo7(int x[volatile const restrict static 7U])
{
}

void foo7Prot(int x[volatile const restrict static 7U]);

void fooStarProt(int x[*]);

int main(void)
{
    return 0;
}
