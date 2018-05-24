public abstract class HierarchyTest {
  // These fields exist only so the classloader will load all test classes:
  HierarchyTestGrandchild field1;
  HierarchyTestChild2 field2;

  abstract void foo();
}

class HierarchyTestChild1 extends HierarchyTest {
  void foo() {}
}

class HierarchyTestChild2 extends HierarchyTest {
  void foo() {}
}

class HierarchyTestGrandchild extends HierarchyTestChild1
  implements HierarchyTestInterface1, HierarchyTestInterface2 {}
