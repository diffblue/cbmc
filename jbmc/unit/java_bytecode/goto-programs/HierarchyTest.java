public class HierarchyTest {
  // These fields exist only so the classloader will load all test classes:
  HierarchyTestGrandchild field1;
  HierarchyTestChild2 field2;
}

class HierarchyTestChild1 extends HierarchyTest {}

class HierarchyTestChild2 extends HierarchyTest {}

class HierarchyTestGrandchild extends HierarchyTestChild1
  implements HierarchyTestInterface1, HierarchyTestInterface2 {}
