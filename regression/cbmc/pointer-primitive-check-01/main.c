
void main()
{
  // we need a new variable for each check, as goto_checkt removes redundant
  // assertions, and if we would use the same variable all pointer primitive
  // assertions would look the same

  char *p1;
  __CPROVER_same_object(p1, p1);

  char *p2;
  __CPROVER_POINTER_OFFSET(p2);

  char *p3;
  __CPROVER_POINTER_OBJECT(p3);

  char *p4;
  __CPROVER_OBJECT_SIZE(p4);

  char *p5;
  __CPROVER_r_ok(p5, 1);

  char *p6;
  __CPROVER_w_ok(p6, 1);

  char *p7;
  __CPROVER_DYNAMIC_OBJECT(p7);
}
