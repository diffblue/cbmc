public class StaticValues extends StaticParent {

  // primitive types
  public static int intField = Util.fib(15);
  public static void testIntPass() {
    assert intField == 610;
  }
  public static void testIntFail() {
    assert intField != 610;
  }

  public static char asciiCharField = 'a';
  public static char hexCharField = '\u0001';
  public static char chineseCharField = '字';
  public static char newLineCharField = '\n';
  public static char specialCharField = '\\';
  public static char fibCharField = (char) Util.fib(15);
  public static void testAsciiCharPass() {
    assert asciiCharField == 'a';
  }
  public static void testAsciiCharFail() {
    assert asciiCharField != 'a';
  }
  public static void testHexCharPass() {
    assert hexCharField == '\u0001';
  }
  public static void testHexCharFail() {
    assert hexCharField != '\u0001';
  }
  public static void testChineseCharPass() {
    assert chineseCharField == '字';
  }
  public static void testChineseCharFail() {
    assert chineseCharField != '字';
  }
  public static void testNewLineCharPass() { assert newLineCharField == '\n'; }
  public static void testNewLineCharFail() { assert newLineCharField != '\n'; }
  public static void testSpecialCharPass() { assert specialCharField == '\\'; }
  public static void testSpecialCharFail() { assert specialCharField != '\\'; }
  public static void testFibCharPass() {
    assert fibCharField == 'ɢ';
  }
  public static void testFibCharFail() {
    assert fibCharField != 'ɢ';
  }

  public static byte byteField = (byte) Util.fib(15);
  public static void testBytePass() {
    assert byteField == 98;
  }
  public static void testByteFail() {
    assert byteField != 98;
  }

  public static boolean booleanField = Util.fib(15) == 610;
  public static void testBooleanPass() {
    assert booleanField;
  }
  public static void testBooleanFail() {
    assert !booleanField;
  }

  public static long longField = Util.fib(15) + 9223372036854775197L;
  public static void testLongPass() {
    assert longField == 9223372036854775807L;
  }
  public static void testLongFail() {
    assert longField != 9223372036854775807L;
  }

  public static short shortField = (short) Util.fib(6);
  public static void testShortPass() {
    assert shortField == 8;
  }
  public static void testShortFail() {
    assert shortField != 8;
  }

  public static double doubleField = Util.fib(6) + 65.23;
  public static void testDoublePass() {
    assert doubleField == 73.23;
  }
  public static void testDoubleFail() {
    assert doubleField != 73.23;
  }

  public static float floatField = Util.fib(6) + 45.12f;
  public static void testFloatPass() {
    assert floatField == 53.12f;
  }
  public static void testFloatFail() {
    assert floatField != 53.12f;
  }

  // null reference types
  public static Foo nullField = null;
  public static void testNullPass() {
    assert nullField == null;
  }
  public static void testNullFail() {
    assert nullField != null;
  }

  // non-null reference types
  public static final Foo foo = new Foo(3,4);
  public static void testReferencePass() {
    assert intField - foo.get() == 593;
  }
  public static void testReferenceFail() {
    assert intField - foo.get() != 593;
  }

  // reference-equal reference types
  public static Foo referenceToOther = foo;
  public static void testReferenceToOtherPass() {
    assert intField - referenceToOther.get() == 593 && referenceToOther == foo;
  }
  public static void testReferenceToOtherFail() {
    assert intField - referenceToOther.get() != 593 || referenceToOther != foo;
  }

  // reference-equal reference types in different classes
  public static Foo referenceToOtherClass = OtherClass.otherField;
  // #KNOWNBUG
  public static void testReferenceToOtherClassPass() {
    assert referenceToOtherClass.get() == 46 && referenceToOtherClass == OtherClass.otherField;
  }
  // #KNOWNBUG
  public static void testReferenceToOtherClassFail() {
    assert referenceToOtherClass.get() != 46 || referenceToOtherClass != OtherClass.otherField;
  }

  // arrays
  public static int[] primitiveArrayField = {Util.fib(5), Util.fib(10), Util.fib(15)};
  public static void testPrimitiveArrayPass() {
    assert primitiveArrayField.length == 3 && primitiveArrayField[0] == 5 &&
        primitiveArrayField[1] == 55 && primitiveArrayField[2] == 610;
  }
  public static void testPrimitiveArrayFail() {
    assert primitiveArrayField.length != 3 || primitiveArrayField[0] != 5 ||
        primitiveArrayField[1] != 55 || primitiveArrayField[2] != 610;
  }
  public static void testPrimitiveArraySumPass() {
    int sum = 0;
    for (int i : primitiveArrayField) {
      sum += i;
    }
    assert sum == 670;
  }
  public static void testPrimitiveArraySumFail() {
    int sum = 0;
    for (int i : primitiveArrayField) {
      sum += i;
    }
    assert sum != 670;
  }

  public static int[] referenceToPrimitiveArray = primitiveArrayField;
  public static void testReferenceToPrimitiveArrayPass() {
    assert referenceToPrimitiveArray == primitiveArrayField;
  }
  public static void testReferenceToPrimitiveArrayFail() {
    assert referenceToPrimitiveArray != primitiveArrayField;
  }

  public static char[] charArrayField = {
    '\u0000', '\u0001', '\u0041', 'B', '?', ';', '\u2FC3'
  };
  public static void testCharArrayPass() {
    assert charArrayField.length == 7 && charArrayField[0] == '\u0000' &&
        charArrayField[1] == '\u0001' && charArrayField[2] == '\u0041' &&
        charArrayField[3] == 'B' && charArrayField[4] == '?' && charArrayField[5] == ';' &&
        charArrayField[6] == '\u2FC3';
  }
  public static void testCharArrayFail() {
    assert charArrayField.length != 7 || charArrayField[0] != '\u0000' ||
        charArrayField[1] != '\u0001' || charArrayField[2] != '\u0041' ||
        charArrayField[3] != 'B' || charArrayField[4] != '?' || charArrayField[5] != ';' ||
        charArrayField[6] != '\u2FC3';
  }


  public static Foo[] referenceArrayField = {new Foo(5, -1), new Foo(6, 7)};
  public static void testReferenceArrayPass() {
    assert referenceArrayField.length == 2 && referenceArrayField[0].get() == 14 &&
        referenceArrayField[1].get() == 23;
  }
  public static void testReferenceArrayFail() {
    assert referenceArrayField.length != 2 || referenceArrayField[0].get() != 14 ||
        referenceArrayField[1].get() != 23;
  }

  public static Foo[] referenceToReferenceArray = referenceArrayField;
  public static void testReferenceToReferenceArrayPass() {
    assert referenceToReferenceArray == referenceArrayField;
  }
  public static void testReferenceToReferenceArrayFail() {
    assert referenceToReferenceArray != referenceArrayField;
  }

  // Primitive wrapper types as static field types
  public static Boolean booleanWrapperField = true;
  public static void testBooleanWrapperPass() { assert booleanWrapperField; }
  public static void testBooleanWrapperFail() { assert !booleanWrapperField; }

  public static Byte byteWrapperField = (byte)50;
  public static void testByteWrapperPass() {
    assert byteWrapperField == (byte)50;
  }
  public static void testByteWrapperFail() {
    assert byteWrapperField != (byte)50;
  }

  public static Character characterWrapperField = '!';
  public static void testCharacterWrapperPass() {
    assert characterWrapperField == '!';
  }
  public static void testCharacterWrapperFail() {
    assert characterWrapperField != '!';
  }

  public static Double doubleWrapperField = 24.56;
  public static void testDoubleWrapperPass() {
    assert doubleWrapperField == 24.56;
  }
  public static void testDoubleWrapperFail() {
    assert doubleWrapperField != 24.56;
  }

  public static Float floatWrapperField = 13.13f;
  public static void testFloatWrapperPass() {
    assert floatWrapperField == 13.13f;
  }
  public static void testFloatWrapperFail() {
    assert floatWrapperField != 13.13f;
  }

  public static Integer integerWrapperField = Util.setTo(1000);
  public static void testIntegerWrapperPass() {
    assert integerWrapperField == 1000;
  }
  public static void testIntegerWrapperFail() {
    assert integerWrapperField != 1000;
  }

  public static Long longWrapperField = 21000000000L;
  public static void testLongWrapperPass() {
    assert longWrapperField == 21000000000L;
  }
  public static void testLongWrapperFail() {
    assert longWrapperField != 21000000000L;
  }

  public static Short shortWrapperField = (short)200;
  public static void testShortWrapperPass() {
    assert shortWrapperField == (short)200;
  }
  public static void testShortWrapperFail() {
    assert shortWrapperField != (short)200;
  }

  // Primitive wrapper types as fields of static field types
  public static ContainerForBoolean booleanWrapperContainer =
      new ContainerForBoolean(true);
  public static void testBooleanWrapperContainerPass() {
    assert booleanWrapperContainer.booleanField;
  }
  public static void testBooleanWrapperContainerFail() {
    assert !booleanWrapperContainer.booleanField;
  }

  public static ContainerForByte byteWrapperContainer =
      new ContainerForByte((byte)50);
  public static void testByteWrapperContainerPass() {
    assert byteWrapperContainer.byteField == (byte)50;
  }
  public static void testByteWrapperContainerFail() {
    assert byteWrapperContainer.byteField != (byte)50;
  }

  public static ContainerForCharacter characterWrapperContainer =
      new ContainerForCharacter('!');
  public static void testCharacterWrapperContainerPass() {
    assert characterWrapperContainer.characterField == '!';
  }
  public static void testCharacterWrapperContainerFail() {
    assert characterWrapperContainer.characterField != '!';
  }

  public static ContainerForDouble doubleWrapperContainer =
      new ContainerForDouble(24.56);
  public static void testDoubleWrapperContainerPass() {
    assert doubleWrapperContainer.doubleField == 24.56;
  }
  public static void testDoubleWrapperContainerFail() {
    assert doubleWrapperContainer.doubleField != 24.56;
  }

  public static ContainerForFloat floatWrapperContainer =
      new ContainerForFloat(13.13f);
  public static void testFloatWrapperContainerPass() {
    assert floatWrapperContainer.floatField == 13.13f;
  }
  public static void testFloatWrapperContainerFail() {
    assert floatWrapperContainer.floatField != 13.13f;
  }

  public static ContainerForInteger integerWrapperContainer =
      new ContainerForInteger(1000);
  public static void testIntegerWrapperContainerPass() {
    assert integerWrapperContainer.integerField == 1000;
  }
  public static void testIntegerWrapperContainerFail() {
    assert integerWrapperContainer.integerField != 1000;
  }

  public static ContainerForLong longWrapperContainer =
      new ContainerForLong(21000000000L);
  public static void testLongWrapperContainerPass() {
    assert longWrapperContainer.longField == 21000000000L;
  }
  public static void testLongWrapperContainerFail() {
    assert longWrapperContainer.longField != 21000000000L;
  }

  public static ContainerForShort shortWrapperContainer =
      new ContainerForShort((short)200);
  public static void testShortWrapperContainerPass() {
    assert shortWrapperContainer.shortField == (short)200;
  }
  public static void testShortWrapperContainerFail() {
    assert shortWrapperContainer.shortField != (short)200;
  }

  public static Integer[] integerWrapperArray = {1111};
  public static void testIntegerWrapperArrayPass() {
    assert integerWrapperArray.length == 1 && integerWrapperArray[0] == 1111;
  }
  public static void testIntegerWrapperArrayFail() {
    assert integerWrapperArray.length != 1 || integerWrapperArray[0] != 1111;
  }

  // Strings
  public static String stringField = Util.repeat("hello! ", 6);
  public static void testStringPass() {
    assert stringField.equals("hello! hello! hello! hello! hello! hello! ");
  }
  public static void testStringFail() {
    assert !stringField.equals("hello! hello! hello! hello! hello! hello! ");
  }

  public static String referenceToString = stringField;
  public static void testReferenceToStringPass1() {
    assert referenceToString.equals("hello! hello! hello! hello! hello! hello! ");
  }
  // #KNOWNBUG
  public static void testReferenceToStringPass2() {
    assert referenceToString == stringField;
  }
  public static void testReferenceToStringFail1() {
    assert !referenceToString.equals("hello! hello! hello! hello! hello! hello! ");
  }
  // #KNOWNBUG
  public static void testReferenceToStringFail2() {
    assert referenceToString != stringField;
  }

  public static StringContainer stringContainerField = new StringContainer();
  public static void testStringContainerPass() {
    assert stringContainerField.contained.equals("abcabcabcabcabc");
  }
  public static void testStringContainerFail() {
    assert !stringContainerField.contained.equals("abcabcabcabcabc");
  }

  // StringBuilder, StringBuffer
  public static StringBuilder stringBuilderField = new StringBuilder(Util.repeat("a", 8));
  public static void testStringBuilderPass() {
    assert stringBuilderField.toString().equals("aaaaaaaa");
  }
  public static void testStringBuilderFail() {
    assert !stringBuilderField.toString().equals("aaaaaaaa");
  }

  public static StringBuffer stringBufferField = new StringBuffer(Util.repeat("b", 6));
  public static void testStringBufferPass() {
    assert stringBufferField.toString().equals("bbbbbb");
  }
  public static void testStringBufferFail() {
    assert !stringBufferField.toString().equals("bbbbbb");
  }

  // generics
  public static GenericType<Foo> genericField = new GenericType<>(new Foo(3, 4));
  public static void testGenericPass() {
    assert genericField.field.get() == 17;
  }
  public static void testGenericFail() {
    assert genericField.field.get() != 17;
  }

  public static GenericMultiDim<Foo, Bar> genericMultiDimField =
      new GenericMultiDim<>(new Foo(2, 8), new Bar(4));
  public static void testGenericMultiDimPass() {
    assert genericMultiDimField.key.get() == 20 && genericMultiDimField.value.get() == 14;
  }
  public static void testGenericMultiDimFail() {
    assert genericMultiDimField.key.get() != 20 || genericMultiDimField.value.get() != 14;
  }

  // enums
  public static Color enumField = Color.WHITE;
  public static void testEnumPass() {
    assert enumField == Color.WHITE && enumField.name().equals("WHITE") &&
        enumField.ordinal() == 3 && enumField.isGrayscale();
  }
  public static void testEnumFail() {
    assert enumField != Color.WHITE || !enumField.name().equals("WHITE") ||
        enumField.ordinal() != 3 || !enumField.isGrayscale();
  }

  // inheritance - static field with inherited fields
  public static MyClassWithInheritedFields myInheriting = new MyClassWithInheritedFields();
  public static void testSubclassFieldPass() {
    assert myInheriting.childField + myInheriting.parentField + myInheriting.parentString.length() == 13;
  }
  public static void testSubclassFieldFail() {
    assert myInheriting.childField + myInheriting.parentField + myInheriting.parentString.length() != 13;
  }

  // inheritance - static field inherited from parent
  public static void testInheritedFieldPass() {
    assert inheritedStatic == 10;
  }
  public static void testInheritedFieldFail() {
    assert inheritedStatic != 10;
  }

  // inheritance - different implementing classes of an interface
  public static MyInterface interfaceFirst = new MyImplementationA();
  public static void testInterfaceFirstPass() {
    assert interfaceFirst.num() == 11;
  }
  public static void testInterfaceFirstFail() {
    assert interfaceFirst.num() != 11;
  }

  public static MyInterface interfaceSecond = new MyImplementationB();
  public static void testInterfaceSecondPass() {
    assert interfaceSecond.num() == 22;
  }
  public static void testInterfaceSecondFail() {
    assert interfaceSecond.num() != 22;
  }

  public static MyInterfaceContainerA interfaceContainerFirst = new MyInterfaceContainerA();
  public static void testInterfaceContainerFirstPass() {
    assert interfaceContainerFirst.getField().num() == 11;
  }
  public static void testInterfaceContainerFirstFail() {
    assert interfaceContainerFirst.getField().num() != 11;
  }

  public static MyInterfaceContainerB interfaceContainerSecond = new MyInterfaceContainerB();
  public static void testInterfaceContainerSecondPass() {
    assert interfaceContainerSecond.getField().num() == 22;
  }
  public static void testInterfaceContainerSecondFail() {
    assert interfaceContainerSecond.getField().num() != 22;
  }

  // inheritance - different implementing classes of an abstract class
  public static MyAbstractClass abstractClassFirst = new MyAbstractImplementationA();
  public static void testAbstractClassFirstPass() {
    assert abstractClassFirst.num() == 11;
  }
  public static void testAbstractClassFirstFail() {
    assert abstractClassFirst.num() != 11;
  }

  public static MyAbstractClass abstractClassSecond = new MyAbstractImplementationB();
  public static void testAbstractClassSecondPass() {
    assert abstractClassSecond.num() == 22;
  }
  public static void testAbstractClassSecondFail() {
    assert abstractClassSecond.num() != 22;
  }

  // inheritance - different subclasses of a concrete class
  public static MyConcreteClass concreteClassFirst = new MySubclassA();
  public static void testConcreteClassFirstPass() {
    assert concreteClassFirst.num() == 20;
  }
  public static void testConcreteClassFirstFail() {
    assert concreteClassFirst.num() != 20;
  }

  public static MyConcreteClass concreteClassSecond = new MySubclassB();
  public static void testConcreteClassSecondPass() {
    assert concreteClassSecond.num() == 30;
  }
  public static void testConcreteClassSecondFail() {
    assert concreteClassSecond.num() != 30;
  }

  // inheritance with generics
  public static GenericInterface<Foo> genericInterfaceSame =
      new GenericImplementation<>(new Foo[]{new Foo(4, 6), new Foo(12, 14)});
  public static void testGenericInterfaceSamePass() {
    assert genericInterfaceSame.size() == 2 && genericInterfaceSame.first().get() == 20 &&
        genericInterfaceSame.num() == 5;
  }
  public static void testGenericInterfaceSameFail() {
    assert genericInterfaceSame.size() != 2 || genericInterfaceSame.first().get() != 20 ||
        genericInterfaceSame.num() != 5;
  }

  public static GenericInterface<Foo> genericInterfaceSimpleMore =
      new GenericImplementationSimpleMore<Foo, Bar>(new Foo(2, 6), new Bar(11));
  public static void testGenericInterfaceSimpleMorePass() {
    assert genericInterfaceSimpleMore.size() == 2 && genericInterfaceSimpleMore.first().get() == 18
        && genericInterfaceSimpleMore.num() == 21;
  }
  public static void testGenericInterfaceSimpleMoreFail() {
    assert genericInterfaceSimpleMore.size() != 2 || genericInterfaceSimpleMore.first().get() != 18
        || genericInterfaceSimpleMore.num() != 21;
  }

  public static GenericInterface<Foo> genericInterfaceMore =
      new GenericImplementationMore<Foo, Bar>(new Foo[]{new Foo(1, 5)}, new Bar[]{new Bar(15), new Bar(12)});
  public static void testGenericInterfaceMorePass() {
    assert genericInterfaceMore.size() == 3 && genericInterfaceMore.first().get() == 16 &&
        genericInterfaceMore.num() == 25;
  }
  public static void testGenericInterfaceMoreFail() {
    assert genericInterfaceMore.size() != 3 || genericInterfaceMore.first().get() != 16 ||
        genericInterfaceMore.num() != 25;
  }

  public static GenericInterface<Foo> genericInterfaceLess =
      new GenericImplementationLess(new Foo[]{new Foo(1, 5)});
  public static void testGenericInterfaceLessPass() {
    assert genericInterfaceLess.size() == 1 && genericInterfaceLess.first().get() == 16 &&
        genericInterfaceLess.num() == 16;
  }
  public static void testGenericInterfaceLessFail() {
    assert genericInterfaceLess.size() != 1 || genericInterfaceLess.first().get() != 16 ||
        genericInterfaceLess.num() != 16;
  }

  public static GenericType<MyInterface> genericWithInterfaceField =
      new GenericType<MyInterface>(new MyImplementationA());
  public static void testGenericWithInterfaceFieldPass() {
    assert genericWithInterfaceField.field.num() == 11;
  }
  public static void testGenericWithInterfaceFieldFail() {
    assert genericWithInterfaceField.field.num() != 11;
  }

}
