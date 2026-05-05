
public class Test {

  public static void main() {

    // First check that all `.class` literals are indeed java.lang.Class
    // instances:
    assert ExampleAnnotation.class instanceof Class;
    assert ExampleInterface.class instanceof Class;
    assert ExampleEnum.class instanceof Class;
    assert ExampleSynthetic.class instanceof Class;
    assert char[].class instanceof Class;
    assert short[].class instanceof Class;
    assert int[].class instanceof Class;
    assert long[].class instanceof Class;
    assert float[].class instanceof Class;
    assert double[].class instanceof Class;
    assert boolean[].class instanceof Class;
    assert Object[].class instanceof Class;
    assert Object[][].class instanceof Class;

    assert ExampleAnnotation.class.isAnnotation();
    assert ExampleInterface.class.isInterface();
    assert ExampleEnum.class.isEnum();
    assert ExampleSynthetic.class.isSynthetic();

    assert char[].class.isArray();
    assert short[].class.isArray();
    assert int[].class.isArray();
    assert long[].class.isArray();
    assert float[].class.isArray();
    assert double[].class.isArray();
    assert boolean[].class.isArray();
    assert Object[].class.isArray();
    assert Object[][].class.isArray();

    // Note use of '==' not '.equals', as we expect the same exact literal,
    // which in jbmc always have the same address.
    // Note names of array classes are not tested yet, as arrays' types are
    // printed as their raw signature, to be addressed separately.
    // Note also primitive types (e.g. int.class) are not addresses here, as
    // they are created through box types' static initializers (e.g. Integer
    // has a static member TYPE that holds the Class for `int.class`)

    assert ExampleAnnotation.class.getName() == "ExampleAnnotation";
    assert ExampleInterface.class.getName() == "ExampleInterface";
    assert ExampleEnum.class.getName() == "ExampleEnum";
    assert ExampleSynthetic.class.getName() == "ExampleSynthetic";

  }

}
