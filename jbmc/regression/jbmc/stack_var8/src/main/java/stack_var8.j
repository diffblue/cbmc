.class public stack_var8
.super java/lang/Object

.field private n I

.method public <init>()V
.limit stack 5
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   aload_0
   iconst_0
   putfield stack_var8/n I
   return
.end method

.method public f()I
   .limit stack 8
   .limit locals 5

   aload_0
   getfield stack_var8/n I
   aload_0
   iconst_1
   putfield stack_var8/n I

   ireturn
.end method
