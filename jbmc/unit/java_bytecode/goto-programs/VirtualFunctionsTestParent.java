
class VirtualFunctionsTestParent {

  // These fields only exist so the classloader will load the children when
  // asked to load the parent:
  VirtualFunctionsTestChild1 c1;
  VirtualFunctionsTestChild2 c2;
  VirtualFunctionsTestGrandchild g;

  public void f() { }

}

class VirtualFunctionsTestChild1 extends VirtualFunctionsTestParent {

  public void f() { }

}

class VirtualFunctionsTestChild2 extends VirtualFunctionsTestParent {

  public void f() { }

}

class VirtualFunctionsTestGrandchild extends VirtualFunctionsTestChild1 {

}
