# C++ Standard Coverage Tracking

This document tracks which rules from the C++ standard (N5008, C++26 draft)
are implemented in CBMC's C++ frontend, and where.  It covers both the
parser (`parse.cpp`) and the type-checker / code-generation files.

## Legend

- ✅ Implemented (with file and function/line reference)
- ⚠️ Partially implemented
- ❌ Not implemented
- ➖ Not applicable (CBMC does not need this rule)
- 🔲 Not yet audited

---

## 4 General principles [basic]

### 4.4 Value categories [basic.lval]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [basic.lval]/1 lvalue/xvalue/prvalue | ✅ | cpp_typecheck_conversions.cpp | xvalue from derived-to-base preserves value category | cpp11_rvalue_ref_derived_to_base |

## 6 Statements [stmt]

### 6.1 Labeled statement [stmt.label]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [stmt.stmt] statement grammar | ✅ | parse.cpp `rStatement` | | |
| [stmt.block] compound statement | ✅ | parse.cpp `rCompoundStatement` | | |
| [stmt.expr] expression statement | ✅ | parse.cpp `rExprStatement` | | |
| [stmt.select] selection statements | ✅ | parse.cpp `rIfStatement`, `rSwitchStatement` | | |
| [stmt.if] if statement | ✅ | parse.cpp `rIfStatement` | C++17 if constexpr in cpp_typecheck_code.cpp | |
| [stmt.switch] switch statement | ✅ | parse.cpp `rSwitchStatement` | | |
| [stmt.iter] iteration statements | ✅ | parse.cpp `rForStatement`, `rWhileStatement`, `rDoStatement` | | |
| [stmt.for] for statement | ✅ | parse.cpp `rForStatement` | Range-for parsed | |
| [stmt.while] while statement | ✅ | parse.cpp `rWhileStatement` | | |
| [stmt.do] do statement | ✅ | parse.cpp `rDoStatement` | | |
| [stmt.dcl] declaration statement | ✅ | parse.cpp `rDeclarationStatement` | C++17 structured bindings in cpp_typecheck_code.cpp | |

## 7 Expressions [expr]

### 7.2.1 Value category [basic.lval]

See section 4.4 above.

### 7.5 Primary expressions [expr.prim]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [expr.prim.general] primary expressions | ✅ | parse.cpp `rPrimaryExpr` | | |
| [expr.prim.lambda] lambda expressions | ⚠️ | parse.cpp `rLambdaExpr` | Parsed; limited type-checking | cpp11_lambda* |
| [expr.prim.req.general] requires-expression | ✅ | parse.cpp `rRequiresExpr` | | |
| [expr.prim.req.simple] simple requirement | ✅ | parse.cpp, cpp_instantiate_template.cpp | `expr;` form | |
| [expr.prim.req.type] type requirement | ✅ | cpp_instantiate_template.cpp | `typename T;` form | |
| [expr.prim.req.compound] compound requirement | ✅ | parse.cpp, cpp_instantiate_template.cpp | `{ expr } -> concept;` | |
| [expr.prim.req.nested] nested requirement | ⚠️ | parse.cpp | `requires constraint-expression;` | |

### 7.6 Compound expressions [expr.compound]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [expr.post] postfix expressions | ✅ | parse.cpp `rPostfixExpr` | | |
| [expr.typeid] typeid | ⚠️ | parse.cpp `rTypeidExpr` | Parsed; limited runtime support | Typeid* |
| [expr.cast] explicit type conversion | ✅ | parse.cpp `rCastExpr` | static_cast, dynamic_cast, const_cast, reinterpret_cast | |
| [expr.unary] unary expressions | ✅ | parse.cpp `rUnaryExpr` | | |
| [expr.unary.noexcept] noexcept operator | ✅ | parse.cpp `rNoexceptExpr`, cpp_typecheck_expr.cpp | Builtins/literals, `noexcept`-declared functions, destructors recognised as noexcept; non-`noexcept` calls and throw-expressions as potentially-throwing | cpp11_noexcept_operator |
| [expr.sizeof] sizeof | ✅ | parse.cpp `rSizeofExpr` | sizeof... for packs | |
| [expr.alignof] alignof | ✅ | parse.cpp `rAlignofExpr` | | |
| [expr.new] new expression | ✅ | parse.cpp `rNewExpr`, builtin_functions.cpp `cpp_new_initializer`, goto_convert.cpp `convert_cpp_delete` | Non-array and array forms both call constructors/destructors per [expr.new]/24, [expr.delete]/6 | New*, cpp11_new_delete, cpp11_array_new_ctor_call |
| [expr.delete] delete expression | ✅ | parse.cpp `rDeleteExpr` | | |
| [expr.mul] multiplicative operators | ✅ | parse.cpp `rMultiplyExpr` | | |
| [expr.add] additive operators | ✅ | parse.cpp `rAdditiveExpr` | | |
| [expr.shift] shift operators | ✅ | parse.cpp `rShiftExpr` | | |
| [expr.rel] relational operators | ✅ | parse.cpp `rRelationalExpr` | | |
| [expr.eq] equality operators | ✅ | parse.cpp `rEqualityExpr` | | |
| [expr.bit.and] bitwise AND | ✅ | parse.cpp `rAndExpr` | | |
| [expr.xor] bitwise XOR | ✅ | parse.cpp `rExclusiveOrExpr` | | |
| [expr.or] bitwise OR | ✅ | parse.cpp `rInclusiveOrExpr` | | |
| [expr.log.and] logical AND | ✅ | parse.cpp `rLogicalAndExpr` | | |
| [expr.log.or] logical OR | ✅ | parse.cpp `rLogicalOrExpr` | | |
| [expr.cond] conditional operator | ✅ | parse.cpp `rConditionalExpr` | | ConditionalExpression* |
| [expr.ass] assignment | ✅ | parse.cpp `rAssignExpr` | | Assignment* |
| [expr.comma] comma operator | ✅ | parse.cpp `rCommaExpr` | Overloaded comma not checked (TODO) | Comma_Operator* |
| [expr.mptr.oper] pointer-to-member | ✅ | parse.cpp `rPmExpr` | .* and ->* | |
| [expr.static.cast] static_cast | ✅ | cpp_typecheck_expr.cpp | | |

## 8 Declarations [dcl.dcl]

### 8.1 Preamble [dcl.pre]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [dcl.dcl] declaration grammar | ✅ | parse.cpp `rDeclaration` | | |
| [dcl.spec] declaration specifiers | ✅ | parse.cpp `rDeclSpecifiers` | | |
| [dcl.stc] storage class specifiers | ✅ | parse.cpp `rStorageSpec` | static, extern, thread_local, mutable | |
| [dcl.typedef] typedef/using declarations | ✅ | parse.cpp `rTypedefDecl`, `rUsingDecl` | C++11 alias declarations | |
| [dcl.type] type specifiers | ✅ | parse.cpp `rTypeSpecifier` | | |
| [dcl.type.simple] simple type specifiers | ✅ | parse.cpp `rSimpleTypeSpecifier` | | |
| [dcl.type.cv] cv-qualifiers | ✅ | parse.cpp `rCvQualify` | | |
| [dcl.enum] enumeration declarations | ✅ | parse.cpp `rEnumSpec` | C++11 scoped enums | Enum* |
| [dcl.align] alignment specifier | ✅ | parse.cpp `rAlignasSpecifier` | alignas | |
| [dcl.attr] attributes | ✅ | parse.cpp `optAttribute` | C++11 [[attr]], scoped attributes | |
| [dcl.attr] [[noreturn]] | ✅ | parse.cpp `optAttribute` | Stored as ID_noreturn | |
| [dcl.attr] [[nodiscard]] | ✅ | parse.cpp `optAttribute` | Stored as ID_nodiscard | |
| [dcl.attr] [[maybe_unused]] | ✅ | parse.cpp `optAttribute` | Consumed and discarded | |
| [dcl.attr] [[carries_dependency]] | ✅ | parse.cpp `optAttribute` | Consumed and discarded | |
| [dcl.attr] scoped attributes | ✅ | parse.cpp `optAttribute` | `gnu::`, `clang::`, `_Clang::`, `msvc::` — consumed and discarded | |
| [dcl.attr] on parameters | ✅ | parse.cpp `rArgDeclaration` | `[[_Clang::__lifetimebound__]]`, `[[gnu::unused]]` on function params | |

### 8.4 Function definitions [dcl.fct.def]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [dcl.fct] function declarators | ✅ | parse.cpp `rDeclarator` | Trailing return types | |
| [dcl.fct]/5 parameter adjustment | ✅ | cpp_typecheck_type.cpp, cpp_typecheck_function.cpp | Array-to-pointer, function-to-pointer | |
| [dcl.fct.spec] function specifiers | ✅ | parse.cpp | virtual, explicit, inline | |
| [dcl.fct.def.default] defaulted functions | ✅ | cpp_typecheck_compound_type.cpp `typecheck_compound_declarator` | = default | |

### 8.5 Structured bindings [dcl.struct.bind]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [dcl.struct.bind] structured bindings | ⚠️ | cpp_typecheck_code.cpp | C++17 auto [a,b] = expr | cpp17_structured_bindings* |

### 8.6 Initializers [dcl.init]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [dcl.init.list] initializer grammar | ✅ | parse.cpp `rInitializeExpr` | | |
| [dcl.init.list]/3.6 non-aggregate brace-init | ✅ | cpp_typecheck_code.cpp `typecheck_return` | Unwrap single-element initializer_list for non-POD | cpp11_brace_init_nonaggregate |
| [dcl.init.list]/3.10 empty brace-init for scalar | ✅ | c_typecheck_initializer.cpp `do_initializer_list` | T{} for scalar produces zero via zero_initializer | cpp11_value_init_scalar_brace |
| [dcl.init.ref]/5 rvalue ref binding | ✅ | cpp_typecheck_expr.cpp, cpp_typecheck_conversions.cpp | Explicit calls + derived-to-base; to_member preserved through address_arithmetic (symex_dereference.cpp) | cpp11_rvalue_ref_derived_to_base, cpp11_addrof_member_compare |

### 8.7 Linkage specifications [dcl.link]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [dcl.link] extern "C"/"C++" | ✅ | parse.cpp `rLinkageSpec` | | |

### 8.8 Pointer-to-member [dcl.mptr]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [dcl.mptr] pointer-to-member declarator | ✅ | parse.cpp `rDeclarator` | | |

## 9 Namespaces [namespace]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [namespace.def] namespace definition | ✅ | parse.cpp `rNamespaceSpec` | Inline namespaces | Namespace* |
| [namespace.udecl] using declaration | ✅ | parse.cpp `rUsing` | | Using* |
| [namespace.udir] using directive | ✅ | parse.cpp `rUsing` | | |

## 11 Classes [class]

### 11.1 Preamble [class.pre]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [class.mem] class members | ✅ | parse.cpp `rClassMember`, cpp_typecheck_compound_type.cpp | | Class_Members* |
| [class.derived] derived classes | ✅ | parse.cpp `rBaseSpec` | | Inheritance* |
| [class.base.init] base/member initializers | ✅ | parse.cpp `rMemberInit` | | Constructor* |
| [class.access.dcl] access declarations | ✅ | parse.cpp `rAccessDecl` | | |
| [class.conv.fct] conversion functions | ✅ | parse.cpp `rConversionDecl` | | Conversion_Operator* |

### 11.4.4 Special member functions [class.special]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [class.default.ctor] default constructor | ✅ | cpp_constructor.cpp `cpp_constructor` | Defaulted default ctor generation | Constructor* |
| [class.copy.ctor]/1 copy constructor | ✅ | cpp_typecheck_constructor.cpp `find_cpctor` | Excludes rvalue refs (move ctors) | Copy_Constructor*, cpp11_class_copy_ctor |
| [class.copy.assign] copy assignment | ✅ | cpp_typecheck_constructor.cpp `default_assignop` | | Copy_Operator* |
| [class.dtor] destructors | ✅ | cpp_destructor.cpp `cpp_destructor` | Virtual destructor dispatch | Destructor* |

### 11.4.5 Constructors and initialization

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| C++11 brace-enclosed init | ✅ | cpp_constructor.cpp | Array and aggregate init | |
| C++11 default member initializers | ✅ | cpp_constructor.cpp, cpp_typecheck_compound_type.cpp | POD and non-POD | |
| C++17 aggregate init with bases | ✅ | cpp_constructor.cpp | | |
| C++20 aggregate parenthesized init | ⚠️ | cpp_constructor.cpp | Basic support | |
| C++11 inheriting constructors | ✅ | cpp_typecheck_compound_type.cpp | using Base::Base | |

### 11.7 Virtual functions [class.virtual]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| Virtual function dispatch | ✅ | cpp_typecheck_virtual_table.cpp `make_vtable_entries`, cpp_typecheck_compound_type.cpp | vtable generation and dispatch | Virtual* |
| Pure virtual functions | ✅ | cpp_typecheck_compound_type.cpp | | virtual1 |
| Virtual destructors | ✅ | cpp_destructor.cpp | Direct call resolution | Destructor* |

## 12 Overloading [over]

### 12.2 Implicit conversion sequences [over.ics]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [conv.lval] lvalue-to-rvalue | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_lvalue_to_rvalue` | | |
| [conv.array] array-to-pointer | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_array_to_pointer` | | |
| [conv.func] function-to-pointer | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_function_to_pointer` | | |
| [conv.qual] qualification conversions | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_qualification` | const/volatile | |
| [conv.prom] integral promotion | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_integral_promotion` | | |
| [conv.fpprom] floating-point promotion | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_floating_point_promotion` | | |
| [conv.integral] integral conversion | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_integral_conversion` | | Conversion* |
| [conv.fpint] floating-integral | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_floating_integral_conversion` | | |
| [conv.double] floating-point conversion | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_floating_point_conversion` | | |
| [conv.ptr] pointer conversions | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_pointer` | null, derived-to-base, void* | |
| [conv.mem] pointer-to-member | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_pointer_to_member` | | |
| [conv.bool] boolean conversions | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_boolean` | | |
| [over.ics.scs] standard conversion sequence | ✅ | cpp_typecheck_conversions.cpp `standard_conversion_sequence` | Chains the above in order | |
| [over.ics.user] user-defined conversion | ✅ | cpp_typecheck_conversions.cpp `user_defined_conversion_sequence` | Converting constructors, conversion operators | Conversion_Operator* |
| [over.ics.ref] reference binding | ✅ | cpp_typecheck_conversions.cpp `reference_binding`, `reference_compatible`, `reference_related` | Lvalue and rvalue reference binding | |
| [over.ics.implicit] implicit conversion | ✅ | cpp_typecheck_conversions.cpp `implicit_conversion_sequence` | Combines standard + user-defined + reference | |
| Implicit typecast dispatch | ✅ | cpp_typecheck_conversions.cpp `implicit_typecast` | Entry point for all implicit conversions | |
| Reference initializer | ✅ | cpp_typecheck_conversions.cpp `reference_initializer` | | |

### 12.3 Explicit type conversions [over.cast]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| const_cast | ✅ | cpp_typecheck_conversions.cpp `const_typecast` | [expr.const.cast] | |
| static_cast | ✅ | cpp_typecheck_conversions.cpp `static_typecast` | [expr.static.cast] | |
| dynamic_cast | ⚠️ | cpp_typecheck_conversions.cpp `dynamic_typecast` | Parsed; limited runtime support | |
| reinterpret_cast | ✅ | cpp_typecheck_conversions.cpp `reinterpret_typecast` | [expr.reinterpret.cast] | |
| cast_away_constness | ✅ | cpp_typecheck_conversions.cpp `cast_away_constness` | Helper for const_cast/reinterpret_cast | |

### 12.4 Overload resolution [over.match]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [over.match] overload resolution | ✅ | cpp_typecheck_resolve.cpp | | |
| [over.match.best] best viable function | ⚠️ | cpp_typecheck_resolve.cpp | | |
| [over.match.list] list-initialization | ⚠️ | cpp_typecheck_initializer.cpp | std::initializer_list argument | |
| [over.oper] operator overloading | ✅ | cpp_declarator_converter.cpp | operator=, [], (), -> | Operator* |

## 13 Templates [temp]

### 13.1 Preamble [temp.pre]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.pre]/1 template-declaration | ✅ | parse.cpp `rTemplateDecl` | | Template* |
| [temp.pre]/2 template-head | ✅ | parse.cpp `rTemplateDecl` | | |
| [temp.pre]/4 requires-clause | ⚠️ | parse.cpp `rTemplateDecl` | Parsed, partially evaluated | |
| [temp.pre]/10 template-id | ✅ | parse.cpp `rTemplateArgs` | | |

### 13.2 Template parameters [temp.param]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.param]/1 type-parameter | ✅ | parse.cpp `rTempArgDeclaration` | class/typename | |
| [temp.param]/2 non-type parameter | ✅ | parse.cpp `rTempArgDeclaration` | | |
| [temp.param]/3 template template parameter | ⚠️ | parse.cpp `rTempArgDeclaration` | Basic support | |
| [temp.param]/4 parameter pack | ⚠️ | parse.cpp, cpp_typecheck_resolve.cpp | Variadic templates partially supported | |
| [temp.param]/14 default arguments | ✅ | parse.cpp `rTempArgDeclaration` | | |

### 13.3 Names of template specializations [temp.names]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.names]/1 simple-template-id | ✅ | parse.cpp `rTemplateArgs` | | |
| [temp.names]/4 `<` disambiguation | ✅ | parse.cpp `maybeTemplateArgs` | Backtracking parser | |

### 13.4 Template arguments [temp.arg]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.arg.type] type arguments | ✅ | cpp_typecheck_resolve.cpp | | |
| [temp.arg.nontype] non-type arguments | ⚠️ | cpp_typecheck_resolve.cpp | Integral constants; C++20 float partial | |
| [temp.arg.template] template template args | ⚠️ | cpp_typecheck_resolve.cpp | Basic support | |

### 13.5 Template constraints [temp.constr]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.constr.constr]/1 constraints | ⚠️ | cpp_instantiate_template.cpp | Concept constraints on specializations | |
| [temp.constr.op] logical operations | ⚠️ | cpp_instantiate_template.cpp | Conjunction in requires-clauses | |
| [temp.constr.atomic] atomic constraints | ⚠️ | cpp_instantiate_template.cpp | Via concept body evaluation | |
| [temp.constr.decl] constrained declarations | ⚠️ | parse.cpp, cpp_instantiate_template.cpp | requires-clause parsing and evaluation | |
| [temp.constr.order] partial ordering by constraints | ⚠️ | cpp_instantiate_template.cpp | Basic ordering in specialization matching | |

### 13.6 Type equivalence [temp.type]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.type]/1 equivalent types | ✅ | cpp_instantiate_template.cpp `template_suffix`, `sub_scope_for_instantiation` | Same template args → same suffix → same symbol | |

### 13.7 Template declarations [temp.decls]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.class.general] class templates | ✅ | cpp_typecheck_template.cpp, cpp_instantiate_template.cpp | | Template* |
| [temp.mem.func] member functions | ✅ | cpp_typecheck_compound_type.cpp | | |
| [temp.deduct.guide] deduction guides | ❌ | | C++17 feature, not implemented | |
| [temp.mem.class] member classes | ✅ | cpp_typecheck_compound_type.cpp | | |
| [temp.static] static data members | ✅ | cpp_typecheck_compound_type.cpp | | |
| [temp.mem] member templates | ⚠️ | cpp_typecheck_template.cpp | | |
| [temp.variadic] variadic templates | ⚠️ | cpp_typecheck_resolve.cpp, cpp_instantiate_template.cpp | Parameter packs, pack expansion, empty/non-empty pack removal | cpp11_variadic_pack_expansion |
| [temp.friend] friends | ⚠️ | cpp_typecheck_compound_type.cpp | | |
| [temp.spec.partial.general] partial specialization | ✅ | cpp_typecheck_template.cpp | | |
| [temp.spec.partial.match] matching | ✅ | cpp_instantiate_template.cpp `elaborate_class_template` | | |
| [temp.spec.partial.order] ordering | ⚠️ | cpp_instantiate_template.cpp | [temp.class.order] referenced | |
| [temp.fct.general] function templates | ✅ | cpp_typecheck_template.cpp | | |
| [temp.over.link] overloading | ⚠️ | cpp_typecheck_resolve.cpp | | |
| [temp.func.order] partial ordering | ⚠️ | cpp_typecheck_resolve.cpp | | |
| [temp.alias] alias templates | ✅ | cpp_typecheck_template.cpp | C++11 | |
| [temp.concept] concept definitions | ⚠️ | parse.cpp, cpp_instantiate_template.cpp | Parsing + evaluation | |

### 13.8 Name resolution [temp.res]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.res.general] general | ⚠️ | cpp_typecheck_resolve.cpp `resolve` | No two-phase lookup; names resolved eagerly | |
| [temp.local] locally declared names | ⚠️ | cpp_typecheck_resolve.cpp | | |
| [temp.dep.type] dependent types | ⚠️ | cpp_typecheck_resolve.cpp | | |
| [temp.dep.expr] type-dependent expressions | ⚠️ | cpp_typecheck_resolve.cpp | | |
| [temp.point] point of instantiation | ✅ | cpp_typecheck_resolve.cpp, cpp_typecheck_template.cpp, cpp_instantiate_template.cpp | Instantiation scope for default args; prefer definition over forward declaration | cpp11_temp_point_definition, cpp20_sort_cpp20 |

### 13.9 Template instantiation [temp.spec]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.inst]/1 implicit instantiation | ✅ | cpp_instantiate_template.cpp `elaborate_class_template` | | cpp11_temp_inst_implicit |
| [temp.inst]/2 unless specialization needed | ✅ | cpp_instantiate_template.cpp | | |
| [temp.explicit] explicit instantiation | ✅ | parse.cpp `rExplicitInstantiation` | | |
| [temp.expl.spec] explicit specialization | ✅ | cpp_typecheck_template.cpp | | |

### 13.10 Function template specializations [temp.fct.spec]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [temp.arg.explicit] explicit template args | ✅ | cpp_typecheck_resolve.cpp | | |
| [temp.deduct.general] deduction general | ✅ | cpp_typecheck_resolve.cpp `guess_template_args` | | |
| [temp.deduct.call]/1 P/A comparison | ✅ | cpp_typecheck_resolve.cpp `guess_function_template_args` | | |
| [temp.deduct.call]/3 forwarding reference | ✅ | cpp_typecheck_resolve.cpp | T&& with lvalue → T& | cpp11_forwarding_ref_deduction |
| [temp.deduct.call]/4 cv-qualification | ✅ | cpp_typecheck_resolve.cpp | cv-stripping, array decay | |
| [temp.deduct.funcaddr] address deduction | ⚠️ | cpp_typecheck_resolve.cpp | Works when target type is a class-template instantiation (e.g. std::endl passed to operator&lt;&lt;); plain function-pointer target types with scalar parameters not yet deduced | cpp11_deduct_funcaddr (KNOWNBUG) |
| [temp.deduct.partial] partial ordering | ⚠️ | cpp_typecheck_resolve.cpp | | |
| [temp.deduct.type]/1 P/A matching | ✅ | cpp_typecheck_resolve.cpp `guess_template_args` (type) | | |
| [temp.deduct.type]/3.3 class specialization | ✅ | cpp_typecheck_resolve.cpp | cpp_name with template_args | |
| [temp.deduct.type]/8 reference stripping | ✅ | cpp_typecheck_resolve.cpp | is_reference branch | |
| [temp.deduct.type]/9 pointer matching | ✅ | cpp_typecheck_resolve.cpp | ID_pointer branch | |
| [temp.deduct.type]/10 array matching | ✅ | cpp_typecheck_resolve.cpp | ID_array branch | |
| [temp.deduct.type]/11 function type matching | ✅ | cpp_typecheck_resolve.cpp | ID_code/ID_function_type branch | |
| [temp.deduct.type]/14 cv-qualified types | ✅ | cpp_typecheck_resolve.cpp | ID_merged_type branch | |
| [temp.over] overload resolution | ✅ | cpp_typecheck_resolve.cpp `resolve` | | |

## 14 Exception handling [except]

| Rule | Status | Location | Notes | Tests |
|------|--------|----------|-------|-------|
| [except.throw] throw expression | ✅ | parse.cpp `rThrowExpr` | | Exception* |
| [except.handle] try/catch | ✅ | parse.cpp `rTryStatement` | | |
| [except.spec] exception specifications | ⚠️ | parse.cpp `optExceptionSpec` | noexcept parsed; dynamic exception specs | |

---

## Known gaps (not implemented)

| Feature | Standard section | Status | Notes |
|---------|-----------------|--------|-------|
| RTTI (dynamic_cast runtime) | [expr.dynamic.cast] | ❌ | Parsed but not modeled at runtime |
| Deduction guides (CTAD) | [temp.deduct.guide] | ❌ | C++17 |
| Coroutines | [dcl.fct.def.coroutine] | ❌ | Stubs for type-checking only |
| Modules | [module] | ❌ | C++20 |
| consteval | [dcl.consteval] | ❌ | C++20 |
| constinit | [dcl.constinit] | ❌ | C++20 |
| Three-way comparison (<=> full) | [expr.spaceship] | ⚠️ | Parsed; partial type support |
| Virtual inheritance (full) | [class.mi] | ⚠️ | Basic support; diamond issues |
| Multiple inheritance (full) | [class.mi] | ⚠️ | Basic vtable; complex cases may fail |
| C++20 concepts grammar | [temp.concept], [temp.constr.constr] | ⚠️ | See "Concepts limitations" below |

---

## Concepts limitations [temp.concept], [temp.constr]

CBMC's concepts support is partial.  Defining `__cpp_concepts`
breaks parsing of some libstdc++ headers, so the macro is not
defined by default and libstdc++ falls back to its pre-C++20
SFINAE / `void_t` paths for detection idioms.  Specifically:

- `parse.cpp:1418-1500` parses the requires-clause skeleton
  (the `requires` keyword followed by a constraint expression),
  but the secondary `requires requires { ... }` form used in
  libstdc++'s `<type_traits>:2655` (positive case of
  `__detected_or` under `__cpp_concepts`) is not parsed
  correctly; pre-defining `__cpp_concepts 202002L` triggers
  parse errors at `type_traits` line 2652 and many others.

- The constraint evaluator in
  `cpp_instantiate_template.cpp:1246-1305` handles
  type/simple/compound/nested requirements when they ARE
  parsed, but the requires-expression bodies that come from
  libstdc++ headers reach it only when the user writes them
  directly (because libstdc++ skips them under
  `!__cpp_concepts`).

- Concept-template-template parameters are not yet supported
  ([temp.arg.template]/3.3 — "A denotes a concept and P is a
  concept template parameter").

- Subsumption ordering between constraints
  ([temp.constr.order]) is implemented at the level of
  primary-template comparison only; cross-specialization
  ordering is not.

The user-facing implication: until `__cpp_concepts` is fully
supported, prefer the `void_t`-based detection idiom in any
constraints CBMC needs to verify.  If you really need concept
syntax in a test case, write the constraint at the user level
(not inside libstdc++ headers) and the existing requires-clause
machinery should evaluate it.

Tracking: when fixing this, note that the strip-tag fix in
`cpp_instantiate_template.cpp` (commit `b0561165bf`) made
namespaced template constexpr eval work — that's a prerequisite
for many concept-evaluation paths since `requires { typename
T::N; }` needs the same eager-conversion machinery.

---

## Files and their primary standard coverage

| File | Primary sections |
|------|-----------------|
| `parse.cpp` | [dcl.*], [stmt.*], [expr.*], [temp.pre], [temp.param], [temp.names], [temp.explicit], [expr.prim.req], [expr.prim.lambda], [except.*], [namespace.*] |
| `cpp_typecheck_template.cpp` | [temp.class.general], [temp.spec.partial.general], [temp.expl.spec], [temp.alias], [temp.fct.general] |
| `cpp_typecheck_resolve.cpp` | [temp.deduct.*], [temp.over], [temp.arg.explicit], [over.match], [temp.point] |
| `cpp_instantiate_template.cpp` | [temp.inst], [temp.spec.partial.match], [temp.constr.*], [expr.prim.req.*], [temp.point] |
| `cpp_typecheck_compound_type.cpp` | [class.mem], [class.virtual], [temp.mem.*], [dcl.fct.def.default] |
| `cpp_typecheck_expr.cpp` | [expr.*], [dcl.init.ref] |
| `cpp_typecheck_conversions.cpp` | [conv.*], [over.ics.*], [basic.lval], [dcl.init.ref], [expr.const.cast], [expr.static.cast], [expr.reinterpret.cast] |
| `cpp_typecheck_code.cpp` | [dcl.init.list], [stmt.*], structured bindings, if constexpr |
| `cpp_typecheck_constructor.cpp` | [class.copy.ctor], [class.copy.assign] |
| `cpp_constructor.cpp` | [class.default.ctor], aggregate/brace initialization |
| `cpp_destructor.cpp` | [class.dtor], virtual destructor dispatch |
| `cpp_typecheck_virtual_table.cpp` | [class.virtual], vtable generation |
| `cpp_declarator_converter.cpp` | [over.oper], symbol creation |
| `cpp_typecheck_initializer.cpp` | [over.match.list], initializer_list |
| `cpp_typecheck_function.cpp` | [dcl.fct]/5, parameter adjustment |
| `cpp_typecheck_type.cpp` | [dcl.fct]/5, array-to-pointer |
| `cpp_typecheck_bases.cpp` | [class.derived], base class scope |
| `template_map.cpp` | [temp.deduct.type] substitution |

---

*Last updated: 2026-05-10*
*Standard reference: N5008 (C++26 draft)*
