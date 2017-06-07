.class public stack_var9
.super java/lang/Object

.field private static n I

.method public <init>()V
.limit stack 5
   aload_0
   invokenonvirtual java/lang/Object/<init>()V
   iconst_0
   putstatic stack_var9/n I
   return
.end method

.method public f()I
   .limit stack 8
   .limit locals 5

   getstatic stack_var9/n I
   iconst_1
   putstatic stack_var9/n I

   ireturn
.end method
