class ClassWithConstructors {
  public ClassWithConstructors() {

  }

  public ClassWithConstructors(int primitiveParam, Object referenceParam, OpaqueClass opaqueParam) {

  }
}

class ClassWithoutConstructors {

}

class ClassWithStaticConstructor {
  static int primitiveA = 4;
  static int primitiveB;
  static int primitiveC;
  static Object referenceA = new Object();
  static Object referenceB;
  static Object referenceC;

  static {
    primitiveB = 5;
    referenceB = new Object();
  }

  public ClassWithStaticConstructor() {

  }

  public ClassWithStaticConstructor(int primitiveParam, Object referenceParam, OpaqueClass opaqueParam) {

  }
}

class StaticClassUsingOpaqueStaticConstructor {
  static int primitiveA = OpaqueClass.primitiveA;
  static int primitiveB = OpaqueClass.primitiveB;
  static int primitiveC = OpaqueClass.primitiveC;
  static Object referenceA = OpaqueClass.referenceA;
  static Object referenceB = OpaqueClass.referenceB;
  static Object referenceC = OpaqueClass.referenceC;
}

class ClassUsingOpaqueStaticConstructor {
  int primitiveA;
  int primitiveB;
  int primitiveC;
  Object referenceA;
  Object referenceB;
  Object referenceC;

  public ClassUsingOpaqueStaticConstructor(){
    primitiveA = OpaqueClass.primitiveA;
    primitiveB = OpaqueClass.primitiveB;
    primitiveC = OpaqueClass.primitiveC;
    referenceA = OpaqueClass.referenceA;
    referenceB = OpaqueClass.referenceB;
    referenceC = OpaqueClass.referenceC;
  }
}

class DummyClassLoadingOpaqueClass {
  DummyClassLoadingOpaqueClass() {
    OpaqueClass o = new OpaqueClass();
    int primitiveA = OpaqueClass.primitiveA;
    int primitiveB = OpaqueClass.primitiveB;
    int primitiveC = OpaqueClass.primitiveC;
    Object referenceA = OpaqueClass.referenceA;
    Object referenceB = OpaqueClass.referenceB;
    Object referenceC = OpaqueClass.referenceC;

  }
}

class OpaqueClass {
  static int primitiveA = 4;
  static int primitiveB;
  static int primitiveC;
  static Object referenceA = new Object();
  static Object referenceB;
  static Object referenceC;

  static {
    primitiveB = 5;
    referenceB = new Object();
  }

  public OpaqueClass() {
    // opaque constructor
  }
}
