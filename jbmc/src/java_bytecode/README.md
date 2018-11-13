\ingroup module_hidden
\defgroup java_bytecode java_bytecode

This module provides a front end for Java.

\section java-bytecode-conversion-section Overview of conversion from bytecode to codet

To be documented.
\subsection java-bytecode-lowering-to-goto Lowering to GOTO

The Java language contains high-level programming concepts like virtual
functions and throw/catch semantics. These need to be rewritten in terms of
other, more fundamental operations in order to analyse the Java program. This
operation is referred to as "lowering". See Background Concepts for more
information.

The following lowering operations are done on Java bytecode after converting
into a basic `codet` representation.

- \ref java-bytecode-runtime-exceptions "Add runtime exceptions"
- \ref java-bytecode-remove-java-new "Remove `new` calls"
- \ref java-bytecode-remove-exceptions "Remove thrown exceptions"
- \ref java-bytecode-remove-instance-of
- As well as other non-Java specific transformations (see \ref goto-programs for
    details on these)

These are performed in `process_goto_function` for example
\ref jbmc_parse_optionst::process_goto_function

Once these lowerings have been completed, you have a GOTO model that can be handled by \ref goto-symex.

\section java-bytecode-array-representation How are Java arrays represented in GOTO

To be documented.

\section java-bytecode-object-factory Object Factory

To be documented.

\subsection java-bytecode-pointer-type-selection Pointer type selection

To be documented.

\subsection java-bytecode-genereic-substitution Generic substitution

To be documented.

\section java-bytecode-parsing Java bytecode parsing (parser, convert_class, convert_method)

To be documented.

\subsection java-class-section How a java program / class is represented in a .class

Every Java class is compiled into a .class file. Inner classes, anonymous
classes or classes for tableswitches are also compiled into their own .class
files.

There exists an [official
specification](https://docs.oracle.com/javase/specs/jvms/se8/html/jvms-4.html)

Each class files contains information about its version, the constant pool,
information about the contained class, its super-class, its implemented
interfaces, its fields, methods and finally additional attributes, such as
information about lambda functions used in the methods of the class or inner
classes the it contains.

The content of a .class file can be inspected via the `javap` tool which is part
of the JDK installation. Useful options are `-c` for code, `-p` to display
protected / private methods `-l` for line numbers and local variable
information, as well as `-verbose` which prints a lot of additional information.

In general, all variable length entries in a class file are represented by first
having an integer `n` that specifies the number of entries and then an array of
`n` such entries in the file. All variable length attribute also contain
information about their length in bytes.

The integer format used in class files are unsigned integers of size 8/16/32
bit, which are named as `u1`/`u2`/`u4`.

\subsection java-class-access-flags Access Flags

The JVM specification defines different access flags, e.g., `final`, `static`,
`protected`, `private` etc. where different ones are applicable to the class
itself, its fields or methods. All access flags are represented as bits, the set
of bits that are defined for one entity is represented as disjunction of those
values. Each of these values is defined as a constant with a name prefixed with
`ACC_` in JBMC, e.g., as `#define ACC_PUBLIC 0x0001` or `#define ACC_ENUM
0x4000`.

\subsection java-class-constant-pool Constant Pool

The constant pool contains all strings and referred values that are used in the
.class. This includes the names of the class itself and its super-class, as well
as the names and signatures of all fields and methods. All strings in the
constant pool are in UTF-16 format.

\subsection java-class-fields Fields

Each member variable of a class has a field entry with a corresponding field
information structure. This contains the name of the field, its raw JVM type
(called the descriptor) and an optional signature.

A signature is an extension to the Java raw types and contains information about
the generic type of an object if applicable.

The name of the field, the descriptor and the signature are all represented as
indices into the constant pool of the class file.

\subsection java-class-methods Methods

Methods are represented in a similar way as fields. Each method has an
associated name, descriptor and optional signature entry in the constant pool
table.

An implemented method also has several attributes. One is the `Code` attribute
that stores the actual bytecode instructions. There is also an optional
`LocalVariableTable` which contains the names of local variables and
parameters. In addition to this there is also an optional
`LocalVariableTypeTable` that contains information about generic local variables
and parameters. Finally the exception table is defined as entries in the
`Exceptions` attribute.

Note: most information about generic types is optional and exists mainly as
debugger information. This is because the Java compiler ensures that typing is
correct and creates code accordingly. The same holds true for information on
local variables. It is therefore advisable to compile Java projects with the
`-g` option that adds debugging information in all cases.

\subsection java-class-attributes Attributes

The last section contains additional attributes, e.g., `SourceFile` which
specified from which source file the .class was compiled, `BootstrapMethods`
which is used for lambda functions or `InnerClasses` which refers to inner
classes of the class in question.


\section java-bytecode-runtime-exceptions Adding runtime exceptions (java_bytecode_instrument)

To be documented.

\section java-bytecode-concurrency-instrumentation Concurrency instrumentation

Relevant code:

  - \ref java_bytecode_concurrency_instrumentation.h
  - \ref java_bytecode_concurrency_instrumentation.cpp
  - \ref java_static_initializers.h
  - \ref java_static_initializers.cpp
  - \ref java_bytecode_convert_method.cpp

Concurrency instrumentation for Java programs is disabled by default. It can
be enabled by specifying the `--java-threading` command line flag.

Thread-blocks have special semantics, in the sense that unlike basic blocks
they can be executed independently.  JBMC treats a sequence of codet's
surrounded with calls to `CProver.startThread:(I)V` and `CProver.endThread:(I)V` as
a thread-block. These functions take one argument, an integer, that is used to
associate the start of a thread (i.e: calls to `CProver.startThread:(I)V`) to the
end of the thread (i.e: calls to `CProver.endThread:(I)V`). JBMC assumes that
calls to the these functions are well-formed, more specifically, each call to
`CProver.startThread:(I)V` must have an associated call to `CProver.endThread:(I)V`.

The instrumentation process (described here) will transform the aforementioned
function calls, synchronized blocks/methods and calls to
`java.lang.Thread.getCurrentThreadID:()I` into appropriate codet. As part of
this process a new variable per thread  is created  along with a single global
variable that is used keep track of thread identifiers. These
variables are needed to handle calls to
`java.lang.Thread.getCurrentThreadID:()I`.

Hold on, how do we go from Java threads to `CProver.startThread:(I)V` and
`CProver.endThread:(I)V`? Well, two ways

  - You are free to use the CProver API and manually and insert calls to the
    `CProver.startThread:(I)V` and `CProver.endThread:(I)V`.
  - Models! Which provide a mock implementation of the `java.lang.Thread`
    class.

Note: instrumentation of Java static initializers changes when the
`--java-threading` flag is specified, this is because the static initializer of
every class needs to be carefully synchronized to prevent superfluous
interleavings.

Note': conversation of synchronized methods (`void synchronized test(){ ... }`) and
synchronized blocks (`synchronized(lock) { ... }`) are dealt with differently as
they are represented differently in bytecode. One is a flag, while the other
has explicit instructions.

\subsection converting-thread-blocks Converting Thread Blocks

JBMC will iterate through the symbol table to find and instrument
thread-blocks.  Specifically, function calls to `CProver.startThread:(I)V` are
transformed into a `codet(id=ID_start_thread, destination=I)`, which carries a target label in
the field `destination`. Similarly `CProver.endThread(I)V` is transformed into
a `codet(id=ID_end_thread)`.

For each new thread a thread local variable `__CPROVER__thread_id` is created.
The new id is obtained by incrementing a global variable
`__CPROVER__next_thread_id`.

The semantics of `codet(id=ID_start_thread, destination=I)` roughly corresponds to: spawn the
current thread, continue the execution of the current thread in the next line,
and continue the execution of the new thread at the destination.

Example, the following Java code:

```java
    CProver.startThread(333);
    ...  // thread body
    CProver.endThread(333);
```

is transformed into the following codet:

```C
  codet(id=ID_start_thread, destination=__CPROVER_THREAD_ENTRY_333)
  codet(id=ID_goto, destination=__CPROVER_THREAD_EXIT_333)
  codet(id=ID_label, label=__CPROVER_THREAD_ENTRY_333)
  codet(id=ID_atomic_begin)
  __CPROVER__next_thread_id += 1;
  __CPROVER__thread_id = __CPROVER__next_thread_id;
  ... // thread body
  codet(id=ID_end_thread)
  codet(id=ID_label, label=__CPROVER_THREAD_EXIT_333)
```

The ID of the thread is made accessible to the Java program by having calls
to the function `CProver.getCurrentThreadID()I` replaced by the variable
`__CPROVER__thread_id`.

Example, the following Java code:

```java
  int g = java.lang.thead.getCurrentThreadID();
```

is transformed into the following codet:

```C
  code_assignt(lhs=g, rhs=__CPROVER__thread_id)
```

\subsection converting-synchronized-blocks Converting Synchronized Blocks

Synchronized blocks make it impossible for two synchronized blocks on the same
object to interleave.

Converting synchronized blocks is rather straightforward as there is a specific
bytecode instruction to indicate the start (`monitorenter`) and end (`monitorexit`)
of a synchronized block.

`monitorenter` is converted to a call to
`java::java.lang.Object.monitorenter:(Ljava/lang/Object;)V`.

`monitorexit` is converted to a call to
`java::java.lang.Object.monitorexit:(Ljava/lang/Object;)V`.

\subsection converting-synchronized-methods Converting Synchronized Methods

Synchronized methods make it impossible for two invocations of the same method
on the same object to interleave.

A method is considered to be synchronized and thus subject to the following
process, if the symbol that represents it has the irep_id `is_synchronized`
specified. In Java this corresponds to the `synchronized` keyword in the
declaration of a method.

Unlike synchronized blocks Java synchronized methods do not have explicit calls
to the instructions `monitorenter` and `monitorexit` (or equivalents), instead
the JVM interprets the synchronized flag  and internally implements
locking/unlocking on the object.

To emulate this behaviour JBMC will iterate through the symbol table to find
synchronized methods. It will then  insert a call to our model of `monitorenter`
(`java::java.lang.Object.monitorenter:(Ljava/lang/Object;)V`) at the beginning
of the method and calls to our model of `monitorexit`
(`java::java.lang.Object.monitorexit:(Ljava/lang/Object;)V`) is instrumented at
each return instruction.  We wrap the entire body of the method with an
exception handler that will call our model of `monitorexit` if the method returns
exceptionally.

Example, the following Java code:

```java
synchronized int amethod(int p)
 {
   int x = 0;
   if(p == 0)
     return -1;
   x = p / 10
   return x
 }
```

The codet version of the above is too verbose be shown here. Instead the following code depicts
our equivalent Java code interpretation of the above:

```java
int amethod(int p)
{
 try
 {
   java::java.lang.Object.monitorenter(this);
   int x = 0;
   if(p == 0)
   {
     java::java.lang.Object.monitorexit(this);
     return -1;
   }
   java::java.lang.Object.monitorexit(this);
   return x
 }
 catch(java::java.lang.Throwable e)
 {
   // catch every exception, including errors!
   java::java.lang.Object.monitorexit(this);
   throw e;
 }
}
```

\section java-bytecode-remove-java-new Remove `new`, `newarray` and `multianewarray` bytecode operators

\ref remove_java_new.h is responsible for converting the `new`, `newarray` and
`multianewarray` Java bytecode operation into \ref codet. Specifically it
converts the bytecode instruction into:  - An ALLOCATE with the size of the
object being created  - An assignment to the value zeroing its contents  - If an
array, initializing the size and data components  - If a multi-dimensional
array, recursively calling `java_new` on each sub array

An ALLOCATE is a \ref side_effect_exprt that is interpreted by \ref
goto_symext::symex_allocate

_Note: it does not call the constructor as this is done by a separate
java_bytecode operation._

\subsection java_objects Java Objects (`new`)

The basic `new` operation is represented in Java bytecode by the `new` op

These are converted by \ref remove_java_newt::lower_java_new

For example, the following Java code:

```java
TestClass f = new TestClass();
```

Which is represented as the following Java bytecode:

```
0: new           #2                  // class TestClass
3: dup
4: invokespecial #3                  // Method "<init>":()V
```

The first instruction only is translated into the following `codet`s:

```cpp
tmp_object1 = side_effect_exprt(ALLOCATE, sizeof(TestClass))
*tmp_object1 = struct_exprt{.component = 0, ... }
```

For more details about the zero expression see \ref expr_initializert

\subsection oned_arrays Single Dimensional Arrays (`newarray`)

The new Java array operation is represented in Java bytecode by the `newarray`
operation.

These are converted by \ref remove_java_newt::lower_java_new_array

See \ref java-bytecode-array-representation for details on how arrays are
represented in codet.

A `newarray` is represented as:
 - an allocation of the array object (the same as with a regular Java object).
 - Initialize the size component
 - Initialize the data component

For example the following Java:

```java
TestClass[] tArray = new TestClass[5];
```

Which is compiled into the following Java bytecode:

```
8: iconst_5
9: anewarray     #2                  // class TestClass
```

Is translated into the following `codet`s:

```cpp
tmp_object1 = side_effect_exprt(ALLOCATE, sizeof(java::array[referenence]))
*tmp_object1 = struct_exprt{.size = 0, .data = null}
tmp_object1->length = length
tmp_new_data_array1 = side_effect_exprt(java_new_array_data, TestClass)
tmp_object1->data = tmp_new_data_array1
ARRAY_SET(tmp_new_data_array1, NULL)
```

The `ARRAY_SET` `codet` sets all the values to null.

\subsection multidarrays Multi Dimensional Arrays (`newmultiarray`)

The new Java multi dimensional array operation is represented in bytecode by
`multianewarray`

These are also by \ref remove_java_newt::lower_java_new_array

They work the same as single dimensional arrays but create a for loop for each
element in the array since these start initialized.

```cpp
for(tmp_index = 0; tmp_index < dim_size; ++tmp_index)
{
  struct java::array[reference] *subarray_init;
  subarray_init = java_new_array
  newarray_tmp1->data[tmp_index] = (void *)subarray_init;
}
```

`remove_java_new` is then recursively applied to the new `subarray`.

\section java-bytecode-remove-exceptions remove_exceptions

To be documented.

\section java-bytecode-remove-instanceof Remove instanceof

\ref remove_instanceof.h removes the bytecode instruction `instanceof ` and replaces it with two instructions:
 - check whether the pointer is null
 - if not null, does the class identifier match the type of any of its subtypes

\section java-bytecode-method-stubbing Method stubbing

To be documented.

\section loading-strategies Loading strategies

Loading strategies are policies that determine what classes and method bodies
are loaded. On an initial pass, the symbols for all classes in all paths on
the Java classpath are loaded. Eager loading is a policy that then loads
all the method bodies for every one of these classes. Lazy loading
strategies are policies that only load class symbols and/or method bodies
when they are in some way requested.

The mechanism used to achieve this is initially common to both eager and
context-insensitive lazy loading. \ref java_bytecode_languaget::typecheck calls
[java_bytecode_convert_class](\ref java_bytecode_languaget::java_bytecode_convert_class)
(for each class loaded by the class loader) to create symbols for all classes
and the methods in them. The methods, along with their parsed representation
(including bytecode) are also added to a map called
\ref java_bytecode_languaget::method_bytecode via a reference held in
\ref java_bytecode_convert_classt::method_bytecode. typecheck then performs a
switch over the value of
[lazy_methods_mode](\ref java_bytecode_languaget::lazy_methods_mode) to
determine which loading strategy to use.

\subsection eager-loading Eager loading

If [lazy_methods_mode](\ref java_bytecode_languaget::lazy_methods_mode) is
\ref java_bytecode_languaget::LAZY_METHODS_MODE_EAGER then eager loading is
used. Under eager loading
\ref java_bytecode_languaget::convert_single_method(const irep_idt &, symbol_table_baset &)
is called once for each method listed in method_bytecode (described above). This
then calls
\ref java_bytecode_languaget::convert_single_method(const irep_idt &, symbol_table_baset &, optionalt<ci_lazy_methods_neededt>)
without a ci_lazy_methods_neededt object, which calls
\ref java_bytecode_convert_method, passing in the method parse tree. This in
turn uses \ref java_bytecode_convert_methodt to turn the bytecode into symbols
for the parameters and local variables and finish populating the symbol for the
method, including converting the instructions to a codet.

\subsection java-bytecode-lazy-methods-v1 Context-Insensitive lazy methods (aka lazy methods v1)

Context-insensitive lazy loading is an alternative method body loading strategy
to eager loading that has been used in Deeptest for a while.
Context-insensitive lazy loading starts at the method given by the `--function`
argument and follows type references (e.g. in the definitions of fields and
method parameters) and function references (at function call sites) to
locate further classes and methods to load. The following paragraph describes
the mechanism used.

If [lazy_methods_mode](\ref java_bytecode_languaget::lazy_methods_mode) is
\ref lazy_methods_modet::LAZY_METHODS_MODE_CONTEXT_INSENSITIVE then
context-insensitive lazy loading is used. Under this stragegy
\ref java_bytecode_languaget::do_ci_lazy_method_conversion is called to do all
conversion. This calls
\ref ci_lazy_methodst::operator()(symbol_tablet &, method_bytecodet &, const method_convertert &),
which creates a work list of methods to check, starting with the entry point,
and classes, starting with the types of any class-typed parameters to the entry
point. For each method in the work list it calls
\ref ci_lazy_methodst::convert_and_analyze_method, which calls the same
java_bytecode_languaget::convert_single_method used by eager loading to do the
conversion (via a `std::function` object passed in via parameter
method_converter) and then calls
\ref ci_lazy_methodst::gather_virtual_callsites to locate virtual calls. Any
classes that may implement an override of the virtual function called are added
to the work list. Finally the symbol table is iterated over and methods that
have been converted, their parameters and local variables, globals accessed
from these methods and classes are kept, everything else is thrown away. This
leaves a symbol table that contains reachable symbols fully populated,
including the instructions for methods converted to a \ref codet.

\section java-bytecode-core-models-library Core Models Library

To be documented.

\section java-bytecode-java-types java_types

To be documented.

\section java-bytecode-string-library String library

To be documented.

See also \ref string-solver-interface.

\section java-bytecode-conversion-example-section A worked example of converting java bytecode to codet

To be documented.
