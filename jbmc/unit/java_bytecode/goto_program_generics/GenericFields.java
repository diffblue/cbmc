public class GenericFields
{
  IWrapper field;
  class SimpleGenericField  {
    Wrapper<IWrapper> field_input;
    public void foo() {
        field_input.field.i = 5;
        field_input.array_field = new IWrapper[2];
    }
  }

  class MultipleGenericFields {
    Wrapper<IWrapper> field_input1;
    Wrapper<BWrapper> field_input2;
    public void foo() {
        field_input1.field.i = 10;
        field_input2.field.b = true;
    }
  }

  class NestedGenericFields {
    Wrapper<Wrapper<IWrapper>> field_input1;
    public void foo() {
        field_input1.field.field.i = 30;
    }
  }

  class PairGenericField {
    PairWrapper<IWrapper, IWrapper> field_input;
    public void foo() {
        field_input.first.i = 40;
        field_input.second.i = 50;
    }
  }

  class GenericMethodParameter {
    public void foo(Wrapper<IWrapper> v) {
        v.field.i = 20;
    }
  }

  class GenericMethodUninstantiatedParameter {
    public <T> void foo_unspec(Wrapper<T> v) {
        v.int_field=10;
    }
  }

  class GenericInnerOuter {
    class Outer<T> {
        public class InnerClass
        {
            T t;
        }

        public Outer()
        {
            field = new InnerClass();
        }

        public InnerClass field;
    }

    public void foo(Outer<Integer> v) {
        Outer t = new Outer<Integer>();
        t.field.t = v.field.t;
    }
  }

  class GenericRewriteParameter {
    class A<T> {
      T value;
      A<Boolean> field;
    }

    public void foo(A<Integer> v) {
      if(v.field.value)
      {
        v.value = 1;
      }
    }
  }
}

// class that implements two generic interfaces
class InterfacesImplementation implements InterfaceWrapper<IWrapper>,
                         InterfacePairWrapper<IWrapper, IWrapper> {
  public IWrapper method(IWrapper t) {
    return t;
  }
  public IWrapper method(IWrapper t, IWrapper tt) {
    if (t.i>0)
    {
      return t;
    }
    else
    {
      return tt;
    }
  }
}
class GenericFieldUnsupported {
  public UnsupportedWrapper2<InterfacesImplementation> f;
  public void foo() {
    f.field.method(new IWrapper(0));
    f.field.method(new IWrapper(0), new IWrapper(2));
  }
}

class GenericFieldOpaque {
  public OpaqueWrapper<IWrapper> f;
  public void foo() {
    f.field.i = 0;
  }
}
