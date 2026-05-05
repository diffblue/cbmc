class IWrapper {
    public int i;
}

class FWrapper {
}

class AWrapper {
}

class SimpleWrapper<T> {
}

public class GenericFields
{
  class SimpleGenericField  {
    // IWrapper field; // for this to work, uncomment this line
    SimpleWrapper<IWrapper> field_input;
    public void foo() {
    }
    SimpleWrapper<IWrapper> f(SimpleWrapper<FWrapper> s, SimpleWrapper<AWrapper []> a) {
      SimpleWrapper<IWrapper> r = new SimpleWrapper<>();
      assert r != null;
      return r;
    }
  }
}
