public class MyClassWithInheritedFields extends MyParent {
  int childField = Util.setTo(4);

  public static int sum(MyClassWithInheritedFields myTemp) {
    int sum = myTemp.childField + myTemp.parentField;
    if (sum == 10)
      return sum;
    return sum;
  }
}
