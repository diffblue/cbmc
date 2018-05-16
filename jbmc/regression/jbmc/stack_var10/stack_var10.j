.class public stack_var10
.super java/lang/Object

.field private static n I

.method public <init>()V
.limit stack 5
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f()I
   .limit stack 8
   .limit locals 5

   iconst_1
   istore_1
   iconst_0
   istore_2
   ;; lvar1 is 1, lvar2 is 0
   iload_1
   iload_2
   ;; on stack 1, 0
   istore_1
   ;; store 0 into lvar1
   ireturn
.end method
