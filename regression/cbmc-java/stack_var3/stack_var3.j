.class public stack_var3
.super java/lang/Object

.method public <init>()V
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   return
.end method

.method public f()I
   .limit stack 5
   .limit locals 3

   ;; 1->var1
   ;; 0->var2
   iconst_1
   istore_1
   iconst_0
   istore_2
   ;; push local var2 / var1
   iload_2
   iload_1
   ;; dup var1
   dup_x1
   ;; sub one from var1
   iinc 1 -1
   ;; pop first var1
   pop
   ;; sub
   isub
   ;; incremented copy on stack
   ireturn
.end method
