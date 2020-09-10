XML Specification for CBMC Traces
=================================

Traces of GOTO programs consist of *steps*, i.e. steps are elements of
the XML object.

Trace Step Types
----------------

-   assignment

-   assume

-   assert

-   goto instruction

-   function call

-   function return

-   output

-   input

-   declaration

-   dead statement

-   spawn statement

-   memory barrier

unused:

-   constraint

-   location

-   shared read

-   shared write

-   atomic begin

-   atomic end

Source Location
---------------

Every trace step optionally contains the source location as an element.

**Attributes** (all are optional):

-   `working-directory`: string of the full path

-   `file`: name of the file containing this location

-   `line`: non-negative integer

-   `column`: non-negative integer

-   `function`: name of the function this line belongs to

**Example**:

``` {.xml}
<location file="test.c" function="main" line="7"
          working-directory="/tmp/subfolder"/>
```

**XSD**:

``` {.xml}
<xs:element name="location">
  <xs:complexType>
    <xs:attribute name="file" type="xs:string" use="optional"/>
    <xs:attribute name="line" type="xs:int" use="optional"/>
    <xs:attribute name="column" type="xs:int" use="optional"/>
    <xs:attribute name="working-directory" type="xs:string"
                  use="optional"/>
    <xs:attribute name="function" type="xs:string" use="optional"/>
  </xs:complexType>
</xs:element>
```

Trace Steps in XML
------------------

The attributes `hidden, thread, step_nr` are common to all trace steps.

``` {.xml}
<xs:attributeGroup name="traceStepAttrs">
  <xs:attribute name="hidden" type="xs:string"></xs:attribute>
  <xs:attribute name="step_nr" type="xs:int"></xs:attribute>
  <xs:attribute name="thread" type="xs:int"></xs:attribute>
</xs:attributeGroup>
```

Assert (element name: `failure`)

**Attributes**:

-   `hidden`: boolean attribute

-   `thread`: thread number (positive integer)

-   `step_nr`: number in the trace (positive integer)

-   `reason`: comment (string)

-   `property`: property ID (irep\_idt)

**Example**:

``` {.xml}
<failure hidden="false" step_nr="23" thread="0"
         property="main.assertion.1"
         reason="assertion a + b &lt; 10">
  <location .. />
</failure>
```

**XSD**:

``` {.xml}
<xs:element name="failure">
  <xs:complexType>
    <xs:all>
      <xs:element name="location" minOccurs="0"></xs:element>
    </xs:all>
    <xs:attributeGroup ref="traceStepAttrs">
    <xs:attribute name="property" type="xs:string"></xs:attribute>
    <xs:attribute name="reason" type="xs:string"></xs:attribute>
  </xs:complexType>
</xs:element>
```

Assignment, Declaration (element name: `assignment`)

**Attributes**:\
if the lhs symbol is known

-   `mode`: {C, Java, ...}

-   `identifier`: string (symbol name)

-   `base_name`: string (e.g. "counter")

-   `display_name`: string (e.g. "main::1::counter")

always present

-   `hidden`: boolean attribute

-   `thread`: thread number (positive integer)

-   `step_nr`: number in the trace (positive integer)

-   `assignment_type`: {actual\_parameter, state}

**Elements**:\
if the lhs symbol is known

-   `type`: C type (e.g. "signed int")

always present

-   `full_lhs`: original lhs expression (after dereferencing)

-   `full_lhs_value`: a constant with the new value.
     - If the type of data can be represented as a fixed width sequence of bits
       then, there will be an attribute `binary` containing the binary
       representation. If the data type is signed and the value is negative
       then the binary will be encoded using two's complement.

**Example**:

``` {.xml}
<assignment assignment_type="state" base_name="b" display_name="main::1::b"
            hidden="false" identifier="main::1::b" mode="C" step_nr="22"
            thread="0">
  <location .. />
  <type>signed int</type>
  <full_lhs>b</full_lhs>
  <full_lhs_value binary="10010000000000000000000000000000">-1879048192</full_lhs_value>
</assignment>
<assignment assignment_type="state" base_name="d" display_name="main::1::d" hidden="false" identifier="main::1::d" mode="C" step_nr="26" thread="0">
  <location file="main.i" function="main" line="3" working-directory="/home/tkiley/workspace/cbmc/regression/cbmc/Float24"/>
  <type>double</type>
  <full_lhs>d</full_lhs>
  <full_lhs_value binary="0100000000010100011001100110011001100110011001100110011001100110">5.1</full_lhs_value>
</assignment>
```

**XSD**:

``` {.xml}
<xs:element name="assignment">
  <xs:complexType>
    <xs:all>
      <xs:element name="location" minOccurs="0"></xs:element>
      <xs:element name="type" type="xs:string" minOccurs="0"></xs:element>
      <xs:element name="full_lhs" type="xs:string"></xs:element>
      <xs:element name="full_lhs_value">
        <xs:complexType>
          <xs:simpleContent>
            <xs:extension base="xs:string">
              <xs:attribute name="binary" type="xs:string"/>
            </xs:extension>
          </xs:simpleContent>
        </xs:complexType>
      </xs:element>
    </xs:all>
    <xs:attributeGroup ref="traceStepAttrs">
    <xs:attribute name="assignment_type" type="xs:string"></xs:attribute>
    <xs:attribute name="base_name" type="xs:string"
                  use="optional"></xs:attribute>
    <xs:attribute name="display_name" type="xs:string"
                  use="optional"></xs:attribute>
    <xs:attribute name="identifier" type="xs:string"
                  use="optional"></xs:attribute>
    <xs:attribute name="mode" type="xs:string" use="optional"></xs:attribute>
  </xs:complexType>
</xs:element>
```

Input (element name: `input`)

**Attributes**:

-   `hidden`: boolean attribute

-   `thread`: thread number (positive integer)

-   `step_nr`: number in the trace (positive integer)

**Elements**:

-   `input_id`: IO id (the variable name)

for each IO argument

-   `value`: the (correctly typed) value the input is initialised with

-   `value_expression`: the internal representation of the value

**Example**:

``` {.xml}
<input hidden="false" step_nr="21" thread="0">
  <input_id>i</input_id>
  <value>-2147145201</value>
  <value_expression>
    <integer binary="10000000000001010010101000001111"
             c_type="int" width="32">
      -2147145201
    </integer>
  </value_expression>
  <location .. />
</input>
```

**XSD**:

``` {.xml}
<xs:element name="input">
  <xs:complexType>
    <xs:sequence>
      <xs:element name="input_id" type="xs:string"/>
      <xs:sequence minOccurs="0" maxOccurs="unbounded">
        <xs:element name="value" type="xs:string"/>
        <xs:element ref="value_expression"/>
      </xs:sequence>
      <xs:element ref="location" minOccurs="0"/>
    </xs:sequence>
    <xs:attributeGroup ref="traceStepAttrs"/>
  </xs:complexType>
</xs:element>
```

Output (element name: `output`)

**Attributes**:

-   `hidden`: boolean attribute

-   `thread`: thread number (positive integer)

-   `step_nr`: number in the trace (positive integer)

**Elements**:

-   `text`: formatted list of IO arguments

for each IO argument

-   `text`: The textual representation of the output

-   `location`: The original source location of the output

-   `value`: the (correctly typed) value of the object that is being
    output

-   `value_expression`: the internal representation of the value

``` {.xml}
<xs:element name="output">
  <xs:complexType>
    <xs:sequence>
      <xs:element name="text" type="xs:string"/>
      <xs:element ref="location" minOccurs="0"/>
      <xs:sequence minOccurs="0" maxOccurs="unbounded">
        <xs:element name="value" type="xs:string"/>
        <xs:element ref="value_expression"/>
      </xs:sequence>
    </xs:sequence>
  <xs:attributeGroup ref="traceStepAttrs"/>
  </xs:complexType>
</xs:element>
```

Function Call (element name: `function_call`)\
Function Return (element name: `function_return`)

**Attributes**:

-   `hidden`: boolean attribute

-   `thread`: thread number (positive integer)

-   `step_nr`: number in the trace (positive integer)

**Elements**:

-   `function`: compound element containing the following\
    Attributes:

    -   `display_name`: language specific pretty name

    -   `identifier`: the internal unique identifier

    Elements:

    -   `location`: source location of the called function

    -   `function`: The function that is being called/returned from.

**Example**:

``` {.xml}
<function_call hidden="false" step_nr="20" thread="0">
  <function display_name="main" identifier="main">
    <location .. />
  </function>
  <location .. />
</function_call>
```

**XSD**:

``` {.xml}
<xs:element name="function_call">
  <xs:complexType>
    <xs:all>
      <xs:element name="location" minOccurs="0"></xs:element>
      <xs:element ref="function"/>
    </xs:all>
    <xs:attributeGroup ref="traceStepAttrs">
  </xs:complexType>
</xs:element>

<xs:element name="function_return">
  <xs:complexType>
    <xs:sequence>
      <xs:element ref="function"/>
      <xs:element ref="location" minOccurs="0"/>
    </xs:sequence>
    <xs:attributeGroup ref="traceStepAttrs"/>
  </xs:complexType>
</xs:element>

<xs:element name="function">
  <xs:complexType>
    <xs:all>
      <xs:element name="location" minOccurs="0"></xs:element>
    </xs:all>
    <xs:attribute name="display_name" type="xs:string"></xs:attribute>
    <xs:attribute name="identifier" type="xs:string"></xs:attribute>
  </xs:complexType>
</xs:element>
```

All Other Steps (element name: `location-only` and `loop-head`)

A step that indicates where in the source program we are.

A `location-only` step is emitted if the source location exists and
differs from the previous one.

A  `loop-head` step is emitted if the location relates to the start of a loop,
even if the previous step is also the same start of the loop (to ensure
that it is printed out for each loop iteration)


**Attributes**:

-   `hidden`: boolean attribute

-   `thread`: thread number (positive integer)

-   `step_nr`: number in the trace (positive integer)

**Elements**:

-   `location`: location of the called function

**Example**:

``` {.xml}
<location-only hidden="false" step_nr="19" thread="0">
  <location .. />
</location-only>
<loop-head hidden="false" step_nr="19" thread="0">
  <location .. />
</loop-head>
```

**XSD**:

``` {.xml}
<xs:element name="location-only">
  <xs:complexType>
    <xs:all>
      <xs:element name="location" minOccurs="0"></xs:element>
    </xs:all>
    <xs:attributeGroup ref="traceStepAttrs">
  </xs:complexType>
</xs:element>

<xs:element name="loop-head">
  <xs:complexType>
    <xs:all>
      <xs:element name="location" minOccurs="0"></xs:element>
    </xs:all>
    <xs:attributeGroup ref="traceStepAttrs">
  </xs:complexType>
</xs:element>
```

Full Trace XSD
--------------

``` {.xml}
<xs:element name="goto_trace">
  <xs:complexType>
    <xs:choice minOccurs="0" maxOccurs="unbounded">
      <xs:element ref="assignment"></xs:element>
      <xs:element ref="failure"></xs:element>
      <xs:element ref="function_call"></xs:element>
      <xs:element ref="function_return"></xs:element>
      <xs:element ref="input"></xs:element>
      <xs:element ref="output"></xs:element>
      <xs:element ref="location-only"></xs:element>
      <xs:element ref="loop-head"></xs:element>
    </xs:choice>
  </xs:complexType>
</xs:element>
```

Notes
-----

The path from the input C code to XML trace goes through the following
steps:\
`C` → `GOTO` → `SSA` → `GOTO Trace` → `XML Trace`

#### SSA to GOTO Trace

SSA steps are sorted by clocks and the following steps are skipped: PHI,
GUARD assignments; shared-read, shared-write, constraint, spawn,
atomic-begin, atomic-end.
