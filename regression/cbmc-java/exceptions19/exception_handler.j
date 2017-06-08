.class exception_handler
.super java/lang/Object

.method public <init>()V
        aload_0
        invokevirtual java/lang/Object/<init>()V
        return
.end method

.method public f()V
        .limit stack 4
        .limit locals 4

      begin:
        new java/lang/Exception
        dup
        invokespecial java/lang/Exception.<init>()V
        athrow
      start:
        nop
      end:
        astore_1
        return
.catch all from begin to end using start
.end method
