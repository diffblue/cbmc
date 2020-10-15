## CBMC Assigns Clause


### Introduction
The _assigns_ clause allows the user to specify a list of memory
locations which may be written within a particular scope. While an assigns
clause may, in general, be interpreted with either _writes_ or _modifies_
semantics, this design is based on the former.  This means that memory not
captured by the assigns clause must not be written within the given scope, even
if the value(s) therein are not modified.


### Scalar Variables
The initial iteration of this design focuses on specifying an assigns clause for
primitive types and their pointers. Arrays, structured data, and pointers are
left to future contributions.


##### Syntax
A special construct is introduced to specify assigns clauses. Its syntax is
defined as follows.

```
 <assigns_clause> := __CPROVER_assigns ( <target_list> )
```
```
 <target_list> := <target>
                | <target> , <target_list>
```
```
 <target> := <identifier>
           | * <target>
```


The `<assigns_clause>` states that only the memory identified by the dereference
expressions and identifiers listed in the contained `<target_list>` may be
written within the associated scope, as follows.


##### Semantics
The semantics of an assigns clause *c* of some function *f* can be understood in
two contexts. First, one may consider how the expressions in *c* are treated
when a call to *f* is replaced by its contract specification, assuming the
contract specification is a sound characterization of the behavior of *f*.
Second, one may consider how *c* is applied to the function body of *f* in order
to determine whether *c* is a sound characterization of the behavior of *f*. We
begin by exploring these two perspectives for assigns clauses which contain only
scalar expressions.

Let the i<sup>th</sup> expression in some assigns clause *c* be denoted
*exprs*<sub>*c*</sub>[i], the j<sup>th</sup> formal parameter of some function
*f* be denoted *params*<sub>*f*</sub>[j], and the k<sup>th</sup> argument passed
in a call to function *f* be denoted *args*<sub>*f*</sub>[k] (an identifying
index may be added to distinguish a *particular* call to *f*, but for simplicity
it is omitted here).


###### Replacement
Assuming an assigns clause *c* is a sound characterization of the behavior of
the function *f*, a call  to *f* may be replaced a series of non-deterministic
assignments. For each expression *e* &#8712; *exprs*<sub>*c*</sub>, let there be
an assignment &#632; := &#8727;, where &#632; is *args*<sub>*f*</sub>[i] if *e*
is identical to some *params*<sub>*f*</sub>[i], and *e* otherwise.


###### Enforcement
In order to determine whether an assigns clause *c* is a sound characterization
of the behavior of a function *f*, the body of the function should be
instrumented with additional statements as follows.

- For each expression *e* &#8712; *exprs*<sub>*c*</sub>, create a temporary
  variable *tmp*<sub>*e*</sub> to store \&(*e*), the address of *e*, at the
start of *f*.
- Before each assignment statement, *lhs* := *rhs*, add an assertion (structured
  as a disjunction)
assert(&#8707; *tmp*<sub>*e*</sub>. \_\_CPROVER\_same\_object(\&(*lhs*),
*tmp*<sub>*e*</sub>)
- Before each function call with an assigns clause *a*, add an assertion for
  each *e*<sub>*a*</sub> &#8712; *exprs*<sub>*a*</sub> (also formulated as a
disjunction)
assert(&#8707; *tmp*<sub>*e*</sub>.
\_\_CPROVER\_same\_object(\&(*e*<sub>*a*</sub>), *tmp*<sub>*e*</sub>)

Here, \_\_CPROVER\_same\_object returns true if two pointers
reference the same object in the CBMC memory model. Additionally, for each
function call without an assigns clause, CBMC adds an assertion assert(*false*)
to ensure that the assigns contract will only hold if all called functions
have an assigns clause which is compatible with that of the calling function.
