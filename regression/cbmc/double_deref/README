This is a batch of tests checking cbmc's behaviour against expressions with more than one deref
operator, such as **p, *(int*)*p, p->field1->field2, etc. At present a directly nested dereference
(**p) is handled by pushing the second deref inside the result of the first. Example:

**p ==>
*(p == &o1 ? o1 : o2) ==>
(p == &o1 ? *o1 : *o2) ==>
(p == &o1 ? (o1 == &o3 ? o3 : o4) : (o2 == &o5 ? o5 : o6))

This deref operator push-in is performed (implicitly) by value_set_dereferencet::dereference, which special-cases
the ternary conditional expression and typecasts of ternary conditionals.
More complicated expressions are handled using a let-expression. Example:

p->field1->field2 ==>
((p == &o1 ? o1 : o2).field1)->field2 ==>
let derefd_pointer = ((p == &o1 ? o1 : o2).field1) in (derefd_pointer == &o3 ? o3 : derefd_pointer == &o4 ? o4 : derefd_pointer == &o5 ? o5 : o6)

Symex executes this let-expression as an auxiliary assignment, such as
derefd_pointer = ((p == &o1 ? o1 : o2).field1)
result = (derefd_pointer == &o3 ? o3 : derefd_pointer == &o4 ? o4 : derefd_pointer == &o5 ? o5 : o6)

The tests in this directory check that auxiliary let-expressions like this are only used when appropriate by inspecting formula VCCs:
double_deref.desc -- a directly nested double-dereference, should not use a let-expression
double_deref_with_cast.desc -- a double-deref with an intervening cast (*(int*)*p for example), should not use a let-expression
double_deref_with_member.desc -- a double-deref with an intervening member expression (p->field1->field2), should use a let-expression
double_deref_with_pointer_arithmetic.desc -- a double-deref with intervening pointer arithmetic (p[idx1][idx2]), should use a let-expression
*_single_alias.desc -- variants of the above where the first dereference points to a single possible object, so no let-expression is necessary
