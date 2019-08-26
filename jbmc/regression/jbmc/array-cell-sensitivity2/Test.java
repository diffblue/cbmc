public class Test {

  public int data;
  public Test[] children = new Test[2];

  public static void main(int unknown) {

    Test[] root = new Test[2];
    Test node1 = new Test();
    Test node2 = new Test();
    root[0] = node1;
    root[1] = node2;
    node1.children[0] = unknown % 2 == 0 ? node1 : node2;
    node1.children[1] = unknown % 3 == 0 ? node1 : node2;
    node2.children[0] = unknown % 5 == 0 ? node1 : node2;
    node2.children[1] = unknown % 7 == 0 ? node1 : node2;
    int idx1 = 0, idx2 = 1, idx3 = 1, idx4 = 0;
    root[idx1].children[idx2].children[idx3].children[idx4].data = 1;
    assert (node1.data == 1);
  }
}
