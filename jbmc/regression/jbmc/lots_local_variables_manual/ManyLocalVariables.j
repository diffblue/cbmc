; This generates a class file that attempts to access local variables indexed
; at 255, 256 and 65534
; The class file is generated from this file using the following command:
; java -jar jasmin.jar ManyLocalVariables.j
; The jasmin jar file can be obtained from: http://jasmin.sourceforge.net/

.class public ManyLocalVariables
.super java/lang/Object

.method public static test()I
  .limit stack 10
  .limit locals 65535
  .line 1
   iconst_1
   istore 1

   iconst_1
   istore 255

   iconst_1
   istore_w 256

   iconst_1
   istore_w 65534

   iload 1
   iload 255
   iload_w 256
   iload_w 65534

   iadd
   iadd
   iadd

   ireturn
.end method
