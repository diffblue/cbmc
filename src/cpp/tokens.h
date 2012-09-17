// tokens

enum {

TOK_IDENTIFIER   = 258, // needs to be bigger than char
TOK_INTEGER,
TOK_CHARACTER,
TOK_FLOATING,
TOK_STRING,
TOK_MULTASSIGN,
TOK_DIVASSIGN,
TOK_MODASSIGN,
TOK_PLUSASSIGN,
TOK_MINUSASSIGN,
TOK_SHLASSIGN,
TOK_SHRASSIGN,
TOK_ANDASSIGN,
TOK_XORASSIGN,
TOK_ORASSIGN,
TOK_EQ,
TOK_NE,
TOK_LE,
TOK_GE,
TOK_SHIFTLEFT,
TOK_SHIFTRIGHT,
TOK_OROR,
TOK_ANDAND,
TOK_INCR,
TOK_DECR,
TOK_SCOPE,
TOK_ELLIPSIS,
TOK_DOTPM,
TOK_ARROWPM,
TOK_ARROW,
TOK_BadToken,
TOK_AUTO,
TOK_CHAR,
TOK_CLASS,
TOK_CONST,
TOK_DELETE,
TOK_DOUBLE,
TOK_ENUM,
TOK_EXTERN,
TOK_FLOAT,
TOK_FRIEND,
TOK_INLINE,
TOK_INT,
TOK_LONG,
TOK_NEW,
TOK_OPERATOR,
TOK_PRIVATE,
TOK_PROTECTED,
TOK_PUBLIC,
TOK_REGISTER,
TOK_SHORT,
TOK_SIGNED,
TOK_STATIC,
TOK_STRUCT,
TOK_TYPEDEF,
TOK_UNION,
TOK_UNSIGNED,
TOK_VIRTUAL,
TOK_VOID,
TOK_VOLATILE,
TOK_TEMPLATE,
TOK_MUTABLE,
TOK_BREAK,
TOK_CASE,
TOK_CONTINUE,
TOK_DEFAULT,
TOK_DO,
TOK_ELSE,
TOK_FOR,
TOK_GOTO,
TOK_IF,
TOK_RETURN,
TOK_SIZEOF,
TOK_SWITCH,
TOK_THIS,
TOK_WHILE,
TOK_ATTRIBUTE,
TOK_BOOL,
TOK_EXTENSION,
TOK_TRY,
TOK_CATCH,
TOK_THROW,
TOK_NAMESPACE,
TOK_USING,
TOK_TYPEID,
TOK_WideStringL,
TOK_WideCharConst,
TOK_WCHAR,
TOK_EXPLICIT,
TOK_TYPENAME,
TOK_WCHAR_T,
TOK_INT8,
TOK_INT16,
TOK_INT32,
TOK_INT64,
TOK_PTR32,
TOK_PTR64,
TOK_COMPLEX,
TOK_REAL,
TOK_IMAG,
TOK_NULLPTR,
TOK_ASM_STRING,
TOK_ALIGNOF,

TOK_Ignore,
TOK_GCC_ASM,
TOK_DECLSPEC,
TOK_TYPEOF,
TOK_MSC_ASM,
TOK_THREAD_LOCAL,
TOK_DECLTYPE,
TOK_CDECL,
TOK_STDCALL,
TOK_FASTCALL,
TOK_CLRCALL,
TOK_STATIC_ASSERT,
TOK_GCC_FLOAT128,
TOK_GCC_INT128,
TOK_CPROVER_BOOL,

// MSC-specific
TOK_INTERFACE,
TOK_MSC_UNARY_TYPE_PREDICATE,
TOK_MSC_BINARY_TYPE_PREDICATE,
TOK_MSC_TRY,
TOK_MSC_EXCEPT,
TOK_MSC_FINALLY,
TOK_MSC_LEAVE,
TOK_MSC_UUIDOF,
TOK_MSC_IF_EXISTS,
TOK_MSC_IF_NOT_EXISTS
};

