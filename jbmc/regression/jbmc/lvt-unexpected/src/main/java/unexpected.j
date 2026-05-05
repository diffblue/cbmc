.class public unexpected
.super java/lang/Object

.method public static test1(I)I
  .limit stack 10
  .limit locals 20

  ; unexpected in previous code, as arg is the argument of the method and its
  ; start_pc is != 0
  .var 0 is arg I from Label1 to Label2
  .var 1 is x   I from Label1 to Label2

  ; say hello
  getstatic      java/lang/System/out Ljava/io/PrintStream;
  ldc            "Starting test1!"
  invokevirtual  java/io/PrintStream/println(Ljava/lang/String;)V

Label1:
  ; x = arg + 3
  iload_0
  iconst_3
  iadd
  istore_1

  ; say bye
  getstatic      java/lang/System/out Ljava/io/PrintStream;
  ldc            "Returning from test1!"
  invokevirtual  java/io/PrintStream/println(Ljava/lang/String;)V

  ; return x
  iload_1
  ireturn
Label2:
.end method
