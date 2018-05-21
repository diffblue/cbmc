.class public stack_var2
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f(I)I
   .limit stack 3
   .limit locals 2

   ;; push local var1
   iload_1
   ;; duplicate
   dup
   ;; increment local var1
   iinc 1 1
   ;; push local var1
   iload_1
   isub
   ;; incremented copy on stack
   ireturn
.end method
