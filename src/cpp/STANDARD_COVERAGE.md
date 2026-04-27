# C++ Standard Coverage Tracking

This document tracks which rules from the C++ standard (N5008, C++26 draft)
are implemented in CBMC's C++ frontend, and where.

## Legend

- ✅ Implemented (with file:line reference)
- ⚠️ Partially implemented
- ❌ Not implemented
- ➖ Not applicable (CBMC does not need this rule)
- 🔲 Not yet audited

## 7 Expressions [expr]

### 7.2.1 Value category [basic.lval]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [basic.lval]/1 xvalue from derived-to-base | ✅ | cpp_typecheck_conversions.cpp | Preserve value category in user_defined_conversion_sequence |

### 7.5.7 Requires expressions [expr.prim.req]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [expr.prim.req.general] grammar | ✅ | parse.cpp `rRequiresExpr` | |
| [expr.prim.req.simple] simple requirements | ✅ | parse.cpp, cpp_instantiate_template.cpp | `expr;` form |
| [expr.prim.req.type] type requirements | ✅ | cpp_instantiate_template.cpp | `typename T;` form |
| [expr.prim.req.compound] compound requirements | ✅ | parse.cpp, cpp_instantiate_template.cpp | `{ expr } -> concept<type>;` |
| [expr.prim.req.nested] nested requirements | ⚠️ | parse.cpp | `requires constraint-expression;` |

## 9 Declarations [dcl]

### 9.4.4 Reference initialization [dcl.init.ref]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [dcl.init.ref]/5 rvalue ref binding | ✅ | cpp_typecheck_expr.cpp, cpp_typecheck_conversions.cpp | Explicit calls + derived-to-base conversion |

### 9.4.5 List-initialization [dcl.init.list]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [dcl.init.list]/3 non-aggregate brace-init | ✅ | cpp_typecheck_code.cpp `typecheck_return` | Unwrap single-element initializer_list for non-POD types |

## 11 Classes [class]

### 11.4.4.2 Copy/move constructors [class.copy.ctor]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [class.copy.ctor]/1 copy ctor definition | ✅ | cpp_typecheck_constructor.cpp `find_cpctor` | Excludes rvalue references (move ctors) |

## 12 Overloading [over]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [over.match] overload resolution | ✅ | cpp_typecheck_resolve.cpp | |
| [over.match.best] best viable function | ⚠️ | cpp_typecheck_resolve.cpp | |

## 13 Templates [temp]

### 13.1 Preamble [temp.pre]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.pre]/1 template-declaration grammar | ✅ | parse.cpp `rTemplateDecl` | |
| [temp.pre]/2 template-head grammar | ✅ | parse.cpp `rTemplateDecl` | |
| [temp.pre]/4 requires-clause | ⚠️ | parse.cpp `rTemplateDecl` | Parsed, partially evaluated |
| [temp.pre]/10 template-id | ✅ | parse.cpp `rTemplateArgs` | |

### 13.2 Template parameters [temp.param]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.param]/1 type-parameter | ✅ | parse.cpp `rTempArgDeclaration` | class/typename |
| [temp.param]/2 non-type parameter | ✅ | parse.cpp `rTempArgDeclaration` | |
| [temp.param]/3 template template parameter | ⚠️ | parse.cpp `rTempArgDeclaration` | Basic support |
| [temp.param]/4 parameter pack | ⚠️ | parse.cpp, cpp_typecheck_resolve.cpp | Variadic templates partially supported |
| [temp.param]/14 default arguments | ✅ | parse.cpp `rTempArgDeclaration` | |

### 13.3 Names of template specializations [temp.names]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.names]/1 simple-template-id | ✅ | parse.cpp `rTemplateArgs` | |
| [temp.names]/4 `<` disambiguation | ✅ | parse.cpp `maybeTemplateArgs` | Backtracking parser |

### 13.4 Template arguments [temp.arg]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.arg.type] type arguments | ✅ | cpp_typecheck_resolve.cpp | |
| [temp.arg.nontype] non-type arguments | ⚠️ | cpp_typecheck_resolve.cpp | Partial: integral constants |
| [temp.arg.template] template template args | ⚠️ | cpp_typecheck_resolve.cpp | Basic support |

### 13.5 Template constraints [temp.constr]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.constr.constr]/1 constraints | ⚠️ | cpp_instantiate_template.cpp | Concept constraints on specializations |
| [temp.constr.op] logical operations | ⚠️ | cpp_instantiate_template.cpp | Conjunction in requires-clauses |
| [temp.constr.atomic] atomic constraints | ⚠️ | cpp_instantiate_template.cpp | Via concept body evaluation |
| [temp.constr.decl] constrained declarations | ⚠️ | parse.cpp, cpp_instantiate_template.cpp | requires-clause parsing and evaluation |
| [temp.constr.order] partial ordering by constraints | ⚠️ | cpp_instantiate_template.cpp | Basic ordering in specialization matching |

### 13.6 Type equivalence [temp.type]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.type]/1 equivalent types | 🔲 | | |

### 13.7 Template declarations [temp.decls]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.class.general] class templates | ✅ | cpp_typecheck_template.cpp, cpp_instantiate_template.cpp | |
| [temp.mem.func] member functions | ✅ | cpp_typecheck_compound_type.cpp | |
| [temp.deduct.guide] deduction guides | ❌ | | C++17 feature, not implemented |
| [temp.mem.class] member classes | ✅ | cpp_typecheck_compound_type.cpp | |
| [temp.static] static data members | ✅ | cpp_typecheck_compound_type.cpp | |
| [temp.mem] member templates | ⚠️ | cpp_typecheck_template.cpp | |
| [temp.variadic] variadic templates | ⚠️ | cpp_typecheck_resolve.cpp | Parameter packs, pack expansion |
| [temp.friend] friends | ⚠️ | cpp_typecheck_compound_type.cpp | |
| [temp.spec.partial.general] partial specialization | ✅ | cpp_typecheck_template.cpp | |
| [temp.spec.partial.match] matching | ✅ | cpp_instantiate_template.cpp `elaborate_class_template` | |
| [temp.spec.partial.order] ordering | ⚠️ | cpp_instantiate_template.cpp | [temp.class.order] referenced |
| [temp.fct.general] function templates | ✅ | cpp_typecheck_template.cpp | |
| [temp.over.link] overloading | ⚠️ | cpp_typecheck_resolve.cpp | |
| [temp.func.order] partial ordering | ⚠️ | cpp_typecheck_resolve.cpp | |
| [temp.alias] alias templates | ✅ | cpp_typecheck_template.cpp:255 | |
| [temp.concept] concept definitions | ⚠️ | parse.cpp, cpp_instantiate_template.cpp | Parsing + evaluation |

### 13.8 Name resolution [temp.res]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.res.general] general | 🔲 | | |
| [temp.local] locally declared names | 🔲 | | |
| [temp.dep.type] dependent types | ⚠️ | cpp_typecheck_resolve.cpp | |
| [temp.dep.expr] type-dependent expressions | ⚠️ | cpp_typecheck_resolve.cpp | |
| [temp.point] point of instantiation | ✅ | cpp_typecheck_resolve.cpp, cpp_typecheck_template.cpp, cpp_instantiate_template.cpp | Use instantiation scope for default non-type args; prefer definition over forward declaration |

### 13.9 Template instantiation and specialization [temp.spec]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.inst]/1 implicit instantiation | ✅ | cpp_instantiate_template.cpp `elaborate_class_template` | |
| [temp.inst]/2 unless specialization needed | ✅ | cpp_instantiate_template.cpp | |
| [temp.explicit] explicit instantiation | ✅ | parse.cpp `rExplicitInstantiation` | |
| [temp.expl.spec] explicit specialization | ✅ | cpp_typecheck_template.cpp | |

### 13.10 Function template specializations [temp.fct.spec]

| Rule | Status | Location | Notes |
|------|--------|----------|-------|
| [temp.arg.explicit] explicit template args | ✅ | cpp_typecheck_resolve.cpp | |
| [temp.deduct.general] deduction general | ✅ | cpp_typecheck_resolve.cpp `guess_template_args` | |
| [temp.deduct.call]/1 P/A comparison | ✅ | cpp_typecheck_resolve.cpp `guess_function_template_args` | |
| [temp.deduct.call]/3 forwarding reference | ✅ | cpp_typecheck_resolve.cpp | rvalue ref + lvalue → lvalue ref |
| [temp.deduct.call]/4 cv-qualification | ✅ | cpp_typecheck_resolve.cpp | cv-stripping for plain T |
| [temp.deduct.funcaddr] address deduction | ✅ | cpp_typecheck_resolve.cpp | Synthetic fargs from known instantiations |
| [temp.deduct.partial] partial ordering | ⚠️ | cpp_typecheck_resolve.cpp | |
| [temp.deduct.type]/1 P/A matching | ✅ | cpp_typecheck_resolve.cpp `guess_template_args` (type) | |
| [temp.deduct.type]/3.3 class specialization | ✅ | cpp_typecheck_resolve.cpp | cpp_name with template_args |
| [temp.deduct.type]/8 reference stripping | ✅ | cpp_typecheck_resolve.cpp | is_reference branch |
| [temp.deduct.type]/9 pointer matching | ✅ | cpp_typecheck_resolve.cpp | ID_pointer branch |
| [temp.deduct.type]/10 array matching | ✅ | cpp_typecheck_resolve.cpp | ID_array branch |
| [temp.deduct.type]/11 function type matching | ✅ | cpp_typecheck_resolve.cpp | ID_code/ID_function_type branch |
| [temp.over] overload resolution | ✅ | cpp_typecheck_resolve.cpp `resolve` | |

---

## Files and their primary standard coverage

| File | Primary sections |
|------|-----------------|
| `parse.cpp` | [temp.pre], [temp.param], [temp.names], [temp.explicit], [expr.prim.req], [expr.prim.lambda] |
| `cpp_typecheck_template.cpp` | [temp.class.general], [temp.spec.partial.general], [temp.expl.spec], [temp.alias] |
| `cpp_typecheck_resolve.cpp` | [temp.deduct.*], [temp.over], [temp.arg.explicit], [over.match] |
| `cpp_instantiate_template.cpp` | [temp.inst], [temp.spec.partial.match], [temp.constr.*], [expr.prim.req.*], [temp.point] |
| `cpp_typecheck_compound_type.cpp` | [temp.mem.func], [temp.mem.class], [temp.static], [class.mem] |
| `cpp_typecheck_expr.cpp` | [expr.*], [conv.*], [dcl.init.ref] |
| `cpp_typecheck_conversions.cpp` | [conv.*], [over.ics], [basic.lval], [dcl.init.ref] |
| `cpp_typecheck_code.cpp` | [dcl.init.list] |
| `cpp_typecheck_constructor.cpp` | [class.copy.ctor] |

---

*Last updated: 2026-04-27*
*Standard reference: N5008 (C++26 draft)*
