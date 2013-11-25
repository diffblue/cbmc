{ "aaload",        0x32, 2, 1, ' ' }, // arrayref, index → value; load onto the stack a reference from an array
{ "aastore",       0x53, 3, 0, ' ' }, // arrayref, index, value →; store into a reference in an array
{ "aconst_null",   0x01, 0, 1, 'a' }, // → null; push a null reference onto the stack
{ "aload",         0x19, 0, 1, 'a' }, // → objectref; load a reference onto the stack from a local variable #index
{ "aload_0",       0x2a, 0, 1, 'a' }, // → objectref; load a reference onto the stack from local variable 0
{ "aload_1",       0x2b, 0, 1, 'a' }, // → objectref; load a reference onto the stack from local variable 1
{ "aload_2",       0x2c, 0, 1, 'a' }, // → objectref; load a reference onto the stack from local variable 2
{ "aload_3",       0x2d, 0, 1, 'a' }, // → objectref; load a reference onto the stack from local variable 3
{ "anewarray",     0xbd, 1, 1, 'a' }, // count → arrayref; create a new array of references of length count and component type identified by the class reference index (indexbyte1 << 8 + indexbyte2) in the constant pool
{ "areturn",       0xb0, 1, 0, ' ' }, // objectref → [empty]; return a reference from a method
{ "arraylength",   0xbe, 1, 1, 'i' }, // arrayref → length; get the length of an array
{ "astore",        0x3a, 1, 0, ' ' }, // objectref →; store a reference into a local variable #index
{ "astore_0",      0x4b, 1, 0, ' ' }, // objectref →; store a reference into local variable 0
{ "astore_1",      0x4c, 1, 0, ' ' }, // objectref →; store a reference into local variable 1
{ "astore_2",      0x4d, 1, 0, ' ' }, // objectref →; store a reference into local variable 2
{ "astore_3",      0x4e, 1, 0, ' ' }, // objectref →; store a reference into local variable 3
{ "athrow",        0xbf, 1, 1, ' ' }, // objectref → [empty], objectref; throws an error or exception (notice that the rest of the stack is cleared, leaving only a reference to the Throwable)
{ "baload",        0x33, 2, 1, 'b' }, // arrayref, index → value; load a byte or Boolean value from an array
{ "bastore",       0x54, 3, 0, ' ' }, // arrayref, index, value →; store a byte or Boolean value into an array
{ "bipush",        0x10, 0, 1, 'i' }, // → value; push a byte onto the stack as an integer value
{ "caload",        0x34, 2, 1, 'c' }, // arrayref, index → value; load a char from an array
{ "castore",       0x55, 3, 0, ' ' }, // arrayref, index, value →; store a char into an array
{ "checkcast",     0xc0, 1, 1, 'a' }, // objectref → objectref; checks whether an objectref is of a certain type, the class reference of which is in the constant pool at index (indexbyte1 << 8 + indexbyte2)
{ "dadd",          0x63, 2, 1, 'd' }, // value1, value2 → result; add two doubles
{ "daload",        0x31, 2, 1, 'd' }, // arrayref, index → value; load a double from an array
{ "dastore",       0x52, 3, 0, ' ' }, // arrayref, index, value →; store a double into an array
{ "dcmpg",         0x98, 2, 1, 'i' }, // value1, value2 → result; compare two doubles
{ "dcmpl",         0x97, 2, 1, 'i' }, // value1, value2 → result; compare two doubles
{ "dconst_0",      0x0e, 0, 1, 'd' }, // → 0.0; push the constant 0.0 onto the stack
{ "dconst_1",      0x0f, 0, 1, 'd' }, // → 1.0; push the constant 1.0 onto the stack
{ "ddiv",          0x6f, 2, 1, 'd' }, // value1, value2 → result; divide two doubles
{ "dload",         0x18, 0, 1, 'd' }, // → value; load a double value from a local variable #index
{ "dload_0",       0x26, 0, 1, 'd' }, // → value; load a double from local variable 0
{ "dload_1",       0x27, 0, 1, 'd' }, // → value; load a double from local variable 1
{ "dload_2",       0x28, 0, 1, 'd' }, // → value; load a double from local variable 2
{ "dload_3",       0x29, 0, 1, 'd' }, // → value; load a double from local variable 3
{ "dmul",          0x6b, 2, 1, 'd' }, // value1, value2 → result; multiply two doubles
{ "dneg",          0x77, 1, 1, 'd' }, // value → result; negate a double
{ "drem",          0x73, 2, 1, 'd' }, // value1, value2 → result; get the remainder from a division between two doubles
{ "dreturn",       0xaf, 1, 0, ' ' }, // value → [empty]; return a double from a method
{ "dstore",        0x39, 1, 0, ' ' }, // value →; store a double value into a local variable #index
{ "dstore_0",      0x47, 1, 0, ' ' }, // value →; store a double into local variable 0
{ "dstore_1",      0x48, 1, 0, ' ' }, // value →; store a double into local variable 1
{ "dstore_2",      0x49, 1, 0, ' ' }, // value →; store a double into local variable 2
{ "dstore_3",      0x4a, 1, 0, ' ' }, // value →; store a double into local variable 3
{ "dsub",          0x67, 2, 1, 'd' }, // value1, value2 → result; subtract a double from another
{ "dup",           0x59, 1, 2, ' ' }, // value → value, value; duplicate the value on top of the stack
{ "dup_x1",        0x5a, 2, 3, ' ' }, // value2, value1 → value1, value2, value1; insert a copy of the top value into the stack two values from the top. value1 and value2 must not be of the type double or long.
{ "dup_x2",        0x5b, 3, 4, ' ' }, // value3, value2, value1 → value1, value3, value2, value1; insert a copy of the top value into the stack two (if value2 is double or long it takes up the entry of value3, too) or three values (if value2 is neither double nor long) from the top
{ "dup2",          0x5c, 2, 4, ' ' }, // {value2, value1} → {value2, value; value2, value1} }, // duplicate top two stack words
{ "dup2_x1",       0x5d, 3, 5, ' ' }, // value3, {value2, value1} → {value2, value; value3, {value2, value1} }, // duplicate two words and insert beneath third word (see explanation above)
{ "dup2_x2",       0x5e, 4, 6, ' ' }, // {value4, value; value2, value1} → {value2, value1}, {value4, value3}, {value2, value1} }, // duplicate two words and insert beneath fourth word
{ "fadd",          0x62, 2, 1, 'f' }, // value1, value2 → result; add two floats
{ "faload",        0x30, 2, 1, 'f' }, // arrayref, index → value; load a float from an array
{ "fastore",       0x51, 3, 0, ' ' }, // arrayref, index, value →; store a float in an array
{ "fcmpg",         0x96, 2, 1, 'i' }, // value1, value2 → result; compare two floats
{ "fcmpl",         0x95, 2, 1, 'i' }, // value1, value2 → result; compare two floats
{ "fconst_0",      0x0b, 0, 1, 'f' }, // → 0.0f; push 0.0f on the stack
{ "fconst_1",      0x0c, 0, 1, 'f' }, // → 1.0f; push 1.0f on the stack
{ "fconst_2",      0x0d, 0, 1, 'f' }, // → 2.0f; push 2.0f on the stack
{ "fdiv",          0x6e, 1, 1, 'f' }, // value1, value2 → result; divide two floats
{ "fload",         0x17, 0, 1, 'f' }, // → value; load a float value from a local variable #index
{ "fload_0",       0x22, 0, 1, 'f' }, // → value; load a float value from local variable 0
{ "fload_1",       0x23, 0, 1, 'f' }, // → value; load a float value from local variable 1
{ "fload_2",       0x24, 0, 1, 'f' }, // → value; load a float value from local variable 2
{ "fload_3",       0x25, 0, 1, 'f' }, // → value; load a float value from local variable 3
{ "fmul",          0x6a, 2, 1, 'f' }, // value1, value2 → result; multiply two floats
{ "fneg",          0x76, 1, 1, 'f' }, // value → result; negate a float
{ "frem",          0x72, 2, 1, 'f' }, // value1, value2 → result; get the remainder from a division between two floats
{ "freturn",       0xae, 1, 0, ' ' }, // value → [empty]; return a float
{ "fstore",        0x38, 1, 0, ' ' }, // value →; store a float value into a local variable #index
{ "fstore_0",      0x43, 1, 0, ' ' }, // value →; store a float value into local variable 0
{ "fstore_1",      0x44, 1, 0, ' ' }, // value →; store a float value into local variable 1
{ "fstore_2",      0x45, 1, 0, ' ' }, // value →; store a float value into local variable 2
{ "fstore_3",      0x46, 1, 0, ' ' }, // value →; store a float value into local variable 3
{ "fsub",          0x66, 2, 1, 'f' }, // value1, value2 → result; subtract two floats
{ "getfield",      0xb4, 1, 1, ' ' }, // objectref → value; get a field value of an object objectref, where the field is identified by field reference in the constant pool index (index1 << 8 + index2)
{ "getstatic",     0xb2, 0, 1, ' ' }, // → value; get a static field value of a class, where the field is identified by field reference in the constant pool index (index1 << 8 + index2)
{ "goto",          0xa7, 0, 0, ' ' }, // [no change]; goes to another instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "goto_w",        0xc8, 0, 0, ' ' }, // [no change]; goes to another instruction at branchoffset (signed int constructed from unsigned bytes branchbyte1 << 24 + branchbyte2 << 16 + branchbyte3 << 8 + branchbyte4)
{ "i2l",           0x85, 1, 1, 'l' }, // value → result; convert an int into a long
{ "i2f",           0x86, 1, 1, 'f' }, // value → result; convert an int into a float
{ "i2d",           0x87, 1, 1, 'd' }, // value → result; convert an int into a double
{ "l2i",           0x88, 1, 1, 'i' }, // value → result; convert a long to a int
{ "l2f",           0x89, 1, 1, 'f' }, // value → result; convert a long to a float
{ "l2d",           0x8a, 1, 1, 'd' }, // value → result; convert a long to a double
{ "f2i",           0x8b, 1, 1, 'i' }, // value → result; convert a float to an int
{ "f2l",           0x8c, 1, 1, 'l' }, // value → result; convert a float to a long
{ "f2d",           0x8d, 1, 1, 'd' }, // value → result; convert a float to a double
{ "d2i",           0x8e, 1, 1, 'i' }, // value → result; convert a double to an int
{ "d2l",           0x8f, 1, 1, 'l' }, // value → result; convert a double to a long
{ "d2f",           0x90, 1, 1, 'f' }, // value → result; convert a double to a float
{ "i2b",           0x91, 1, 1, 'b' }, // value → result; convert an int into a byte
{ "i2c",           0x92, 1, 1, 'c' }, // value → result; convert an int into a character
{ "i2s",           0x93, 1, 1, 's' }, // value → result; convert an int into a short
{ "iadd",          0x60, 2, 1, 'i' }, // value1, value2 → result; add two ints
{ "iaload",        0x2e, 2, 1, 'i' }, // arrayref, index → value; load an int from an array
{ "iand",          0x7e, 2, 1, 'i' }, // value1, value2 → result; perform a bitwise and on two integers
{ "iastore",       0x4f, 3, 0, ' ' }, // arrayref, index, value →; store an int into an array
{ "iconst_m1",     0x02, 0, 1, 'i' }, // → -1; load the int value -1 onto the stack
{ "iconst_0",      0x03, 0, 1, 'i' }, // → 0; load the int value 0 onto the stack
{ "iconst_1",      0x04, 0, 1, 'i' }, // → 1; load the int value 1 onto the stack
{ "iconst_2",      0x05, 0, 1, 'i' }, // → 2; load the int value 2 onto the stack
{ "iconst_3",      0x06, 0, 1, 'i' }, // → 3; load the int value 3 onto the stack
{ "iconst_4",      0x07, 0, 1, 'i' }, // → 4; load the int value 4 onto the stack
{ "iconst_5",      0x08, 0, 1, 'i' }, // → 5; load the int value 5 onto the stack
{ "idiv",          0x6c, 2, 1, 'i' }, // value1, value2 → result; divide two integers
{ "if_acmpeq",     0xa5, 2, 0, ' ' }, // value1, value2 →; if references are equal, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "if_acmpne",     0xa6, 2, 0, ' ' }, // value1, value2 →; if references are not equal, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "if_icmpeq",     0x9f, 2, 0, ' ' }, // value1, value2 →; if ints are equal, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "if_icmpne",     0xa0, 2, 0, ' ' }, // value1, value2 →; if ints are not equal, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "if_icmplt",     0xa1, 2, 0, ' ' }, // value1, value2 →; if value1 is less than value2, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "if_icmpge",     0xa2, 2, 0, ' ' }, // value1, value2 →; if value1 is greater than or equal to value2, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "if_icmpgt",     0xa3, 2, 0, ' ' }, // value1, value2 →; if value1 is greater than value2, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "if_icmple",     0xa4, 2, 0, ' ' }, // value1, value2 →; if value1 is less than or equal to value2, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "ifeq",          0x99, 1, 0, ' ' }, // value →; if value is 0, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "ifne",          0x9a, 1, 0, ' ' }, // value →; if value is not 0, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "iflt",          0x9b, 1, 0, ' ' }, // value →; if value is less than 0, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "ifge",          0x9c, 1, 0, ' ' }, // value →; if value is greater than or equal to 0, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "ifgt",          0x9d, 1, 0, ' ' }, // value →; if value is greater than 0, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "ifle",          0x9e, 1, 0, ' ' }, // value →; if value is less than or equal to 0, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "ifnonnull",     0xc7, 1, 0, ' ' }, // value →; if value is not null, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "ifnull",        0xc6, 1, 0, ' ' }, // value →; if value is null, branch to instruction at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2)
{ "iinc",          0x84, 0, 0, ' ' }, // [No change]; increment local variable #index by signed byte const
{ "iload",         0x15, 0, 1, 'i' }, // → value; load an int value from a local variable #index
{ "iload_0",       0x1a, 0, 1, 'i' }, // → value; load an int value from local variable 0
{ "iload_1",       0x1b, 0, 1, 'i' }, // → value; load an int value from local variable 1
{ "iload_2",       0x1c, 0, 1, 'i' }, // → value; load an int value from local variable 2
{ "iload_3",       0x1d, 0, 1, 'i' }, // → value; load an int value from local variable 3
{ "imul",          0x68, 2, 1, 'i' }, // value1, value2 → result; multiply two integers
{ "ineg",          0x74, 1, 1, 'i' }, // value → result; negate int
{ "instanceof",    0xc1, 1, 1, ' ' }, // objectref → result; determines if an object objectref is of a given type, identified by class reference index in constant pool (indexbyte1 << 8 + indexbyte2)
{ "invokedynamic", 0xba, 0, 0, ' ' }, // [arg1, [arg2 ...]] →; invokes a dynamic method identified by method reference index in constant pool (indexbyte1 << 8 + indexbyte2)
{ "invokeinterface",0xb9,0, 0, ' ' }, // objectref, [arg1, arg2, ...] →; invokes an interface method on object objectref, where the interface method is identified by method reference index in constant pool (indexbyte1 << 8 + indexbyte2)
{ "invokespecial", 0xb7, 0, 0, ' ' }, // objectref, [arg1, arg2, ...] →; invoke instance method on object objectref, where the method is identified by method reference index in constant pool (indexbyte1 << 8 + indexbyte2)
{ "invokestatic",  0xb8, 0, 0, ' ' }, // [arg1, arg2, ...] →; invoke a static method, where the method is identified by method reference index in constant pool (indexbyte1 << 8 + indexbyte2)
{ "invokevirtual", 0xb6, 0, 0, ' ' }, // objectref, [arg1, arg2, ...] →; invoke virtual method on object objectref, where the method is identified by method reference index in constant pool (indexbyte1 << 8 + indexbyte2)
{ "ior",           0x80, 2, 1, 'i' }, // value1, value2 → result; bitwise int or
{ "irem",          0x70, 2, 1, 'i' }, // value1, value2 → result; logical int remainder
{ "ireturn",       0xac, 1, 0, ' ' }, // value → [empty]; return an integer from a method
{ "ishl",          0x78, 2, 1, 'i' }, // value1, value2 → result; int shift left
{ "ishr",          0x7a, 2, 1, 'i' }, // value1, value2 → result; int arithmetic shift right
{ "istore",        0x36, 1, 0, ' ' }, // value →; store int value into variable #index
{ "istore_0",      0x3b, 1, 0, ' ' }, // value →; store int value into variable 0
{ "istore_1",      0x3c, 1, 0, ' ' }, // value →; store int value into variable 1
{ "istore_2",      0x3d, 1, 0, ' ' }, // value →; store int value into variable 2
{ "istore_3",      0x3e, 1, 0, ' ' }, // value →; store int value into variable 3
{ "isub",          0x64, 2, 1, 'i' }, // value1, value2 → result; int subtract
{ "iushr",         0x7c, 2, 1, 'i' }, // value1, value2 → result; int logical shift right
{ "ixor",          0x82, 2, 1, 'i' }, // value1, value2 → result; int xor
{ "jsr",           0xa8, 0, 1, 'a' }, // → address; jump to subroutine at branchoffset (signed short constructed from unsigned bytes branchbyte1 << 8 + branchbyte2) and place the return address on the stack
{ "jsr_w",         0xc9, 0, 1, 'a' }, // → address; jump to subroutine at branchoffset (signed int constructed from unsigned bytes branchbyte1 << 24 + branchbyte2 << 16 + branchbyte3 << 8 + branchbyte4) and place the return address on the stack
{ "ladd",          0x61, 2, 1, 'l' }, // value1, value2 → result; add two longs
{ "laload",        0x2f, 2, 1, 'l' }, // arrayref, index → value; load a long from an array
{ "land",          0x7f, 2, 1, 'l' }, // value1, value2 → result; bitwise and of two longs
{ "lastore",       0x50, 3, 0, ' ' }, // arrayref, index, value →; store a long to an array
{ "lcmp",          0x94, 2, 1, 'i' }, // value1, value2 → result; compare two long values
{ "lconst_0",      0x09, 0, 1, 'l' }, // → 0L; push the long 0 onto the stack
{ "lconst_1",      0x0a, 0, 1, 'l' }, // → 1L; push the long 1 onto the stack
{ "ldc",           0x12, 0, 1, ' ' }, // → value; push a constant #index from a constant pool (String, int or float) onto the stack
{ "ldc_w",         0x13, 0, 1, ' ' }, // → value; push a constant #index from a constant pool (String, int or float) onto the stack (wide index is constructed as indexbyte1 << 8 + indexbyte2)
{ "ldc2_w",        0x14, 0, 1, ' ' }, // → value; push a constant #index from a constant pool (double or long) onto the stack (wide index is constructed as indexbyte1 << 8 + indexbyte2)
{ "ldiv",          0x6d, 2, 1, 'l' }, // value1, value2 → result; divide two longs
{ "lload",         0x16, 0, 1, 'l' }, // → value; load a long value from a local variable #index
{ "lload_0",       0x1e, 0, 1, 'l' }, // → value; load a long value from a local variable 0
{ "lload_1",       0x1f, 0, 1, 'l' }, // → value; load a long value from a local variable 1
{ "lload_2",       0x20, 0, 1, 'l' }, // → value; load a long value from a local variable 2
{ "lload_3",       0x21, 0, 1, 'l' }, // → value; load a long value from a local variable 3
{ "lmul",          0x69, 2, 1, 'l' }, // value1, value2 → result; multiply two longs
{ "lneg",          0x75, 1, 1, 'l' }, // value → result; negate a long
{ "lookupswitch",  0xab, 1, 0, ' ' }, // key →; a target address is looked up from a table using a key and execution continues from the instruction at that address
{ "lor",           0x81, 2, 1, 'l' }, // value1, value2 → result; bitwise or of two longs
{ "lrem",          0x71, 2, 1, 'l' }, // value1, value2 → result; remainder of division of two longs
{ "lreturn",       0xad, 1, 0, ' ' }, // value → [empty]; return a long value
{ "lshl",          0x79, 2, 1, 'l' }, // value1, value2 → result; bitwise shift left of a long value1 by value2 positions
{ "lshr",          0x7b, 2, 1, 'l' }, // value1, value2 → result; bitwise shift right of a long value1 by value2 positions
{ "lstore",        0x37, 1, 0, ' ' }, // value →; store a long value in a local variable #index
{ "lstore_0",      0x3f, 1, 0, ' ' }, // value →; store a long value in a local variable 0
{ "lstore_1",      0x40, 1, 0, ' ' }, // value →; store a long value in a local variable 1
{ "lstore_2",      0x41, 1, 0, ' ' }, // value →; store a long value in a local variable 2
{ "lstore_3",      0x42, 1, 0, ' ' }, // value →; store a long value in a local variable 3
{ "lsub",          0x65, 2, 1, 'l' }, // value1, value2 → result; subtract two longs
{ "lushr",         0x7d, 2, 1, 'l' }, // value1, value2 → result; bitwise shift right of a long value1 by value2 positions, unsigned
{ "lxor",          0x83, 2, 1, 'l' }, // value1, value2 → result; bitwise exclusive or of two longs
{ "monitorenter",  0xc2, 1, 0, ' ' }, // objectref →; enter monitor for object ("grab the lock" - start of synchronized() section)
{ "monitorexit",   0xc3, 1, 0, ' ' }, // objectref →; exit monitor for object ("release the lock" - end of synchronized() section)
{ "multianewarray",0xc5, 0, 1, 'a' }, // count1, [count2,...] → arrayref; create a new array of dimensions dimensions with elements of type identified by class reference in constant pool index (indexbyte1 << 8 + indexbyte2); the sizes of each dimension is identified by count1, [count2, etc.]
{ "new",           0xbb, 0, 1, 'a' }, // → objectref; create new object of type identified by class reference in constant pool index (indexbyte1 << 8 + indexbyte2)
{ "newarray",      0xbc, 1, 1, 'a' }, // count → arrayref; create new array with count elements of primitive type identified by atype
{ "nop",           0x00, 0, 0, ' ' }, // [No change]; perform no operation
{ "pop",           0x57, 1, 0, ' ' }, // value →; discard the top value on the stack
{ "pop2",          0x58, 2, 0, ' ' }, // {value2, value1} →; discard the top two values on the stack (or one value, if it is a double or long)
{ "putfield",      0xb5, 2, 0, ' ' }, // objectref, value →; set field to value in an object objectref, where the field is identified by a field reference index in constant pool (indexbyte1 << 8 + indexbyte2)
{ "putstatic",     0xb3, 1, 0, ' ' }, // value →; set static field to value in a class, where the field is identified by a field reference index in constant pool (indexbyte1 << 8 + indexbyte2)
{ "ret",           0xa9, 0, 0, ' ' }, // [No change]; continue execution from address taken from a local variable #index (the asymmetry with jsr is intentional)
{ "return",        0xb1, 0, 0, ' ' }, // → [empty]; return void from method
{ "saload",        0x35, 2, 1, 's' }, // arrayref, index → value; load short from array
{ "sastore",       0x56, 3, 0, 's' }, // arrayref, index, value →; store short to array
{ "sipush",        0x11, 0, 1, 's' }, // → value; push a short onto the stack
{ "swap",          0x5f, 2, 2, ' ' }, // value2, value1 → value1, value2; swaps two top words on the stack (note that value1 and value2 must not be double or long)
{ "tableswitch",   0xaa, 1, 0, ' ' }, // index →; continue execution from an address in the table at offset index
{ "breakpoint",    0xca, 0, 0, ' ' }, // ; reserved for breakpoints in Java debuggers; should not appear in any class file
{ "impdep1",       0xfe, 0, 0, ' ' }, // ; reserved for implementation-dependent operations within debuggers; should not appear in any class file
{ "impdep2",       0xff, 0, 0, ' ' }, // ; reserved for implementation-dependent operations within debuggers; should not appear in any class file
{ 0, 0 }  
