public class Test {

  // This tests the case where multiple interfaces define the same function--
  // the interface should still be a valid functional interface even
  // though its one abstract method satisfies more than one type, or a single
  // type that is inherited by multiple routes.

  interface If1 {
    int f(int x);
  }

  interface If2 {
    int f(int x);
  }

  interface DirectMerge extends If1, If2 { }

  interface Parent extends If1 { }
  interface MergeViaParent extends Parent, If2 { }

  interface MergeWithSameInterface extends Parent, If1 { }

  interface DirectMergeRedeclare extends If1, If2 { int f(int x); }
  interface MergeViaParentRedeclare extends Parent, If2 { int f(int x); }
  interface MergeWithSameInterfaceRedeclare extends Parent, If1 { int f(int x); }

  public static void main() {

    DirectMerge test1 = (x -> x + 1);
    MergeViaParent test2 = (x -> x + 1);
    MergeWithSameInterface test3 = (x -> x + 1);
    DirectMergeRedeclare test4 = (x -> x + 1);
    MergeViaParentRedeclare test5 = (x -> x + 1);
    MergeWithSameInterfaceRedeclare test6 = (x -> x + 1);

    assert test1.f(1) == 2;
    assert test2.f(1) == 2;
    assert test3.f(1) == 2;
    assert test4.f(1) == 2;
    assert test5.f(1) == 2;
    assert test6.f(1) == 2;
    assert false; // Check we got here

  }

}
