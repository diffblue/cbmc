// Detect parameters of cheap-to-copy types passed by const reference.
//
// Implements C++ Core Guidelines F.16 ("for `in` parameters, pass cheaply
// copied types by value and others by reference to const"). The set of
// "cheap" types is configured below in CHEAP_TYPES; it currently lists
// dstringt (= irep_idt), which is a wrapper around a single unsigned
// table index and is strictly cheaper to copy than to take by reference.
//
// The matcher is `parmVarDecl()`. Real method/function parameters and
// named parameters of function-type template arguments inside
// *instantiated* class templates (e.g.
// `std::function<void(const key_type &k)>` inside `sharing_mapt<K, V>`
// when instantiated with K = irep_idt) are flagged. --fix can rewrite
// the former in place; the latter are flagged but not auto-rewritten,
// because changing the in-class declaration without the matching
// out-of-class definition would not compile.
//
// Limitation: anonymous parameters in non-instantiated typedefs of
// std::function (e.g. `using cb = std::function<void(const irep_idt &)>`)
// don't produce a ParmVarDecl in Clang's AST and therefore are not
// caught here. A complementary `FunctionProtoTypeLoc` walker would
// close this gap; for now, regressions of that specific shape need
// to be caught by code review or a follow-up grep sweep.
//
// Build:
//   clang++-18 -o check-pass-by-value scripts/check_pass_by_value.cpp \
//     $(llvm-config-18 --cxxflags | sed 's/-Werror//g') \
//     -L/usr/lib/llvm-18/lib -lclang-cpp \
//     $(llvm-config-18 --ldflags --libs --system-libs) -fno-rtti
//
// Usage (check):
//   ./check-pass-by-value -p build/compile_commands.json src/foo/*.cpp
// Usage (rewrite in-place):
//   ./check-pass-by-value --fix -p build/compile_commands.json src/foo/*.cpp

#include <set>
#include <string>

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::tooling;

static llvm::cl::OptionCategory Cat("check-pass-by-value");
static llvm::cl::opt<bool> Fix(
  "fix",
  llvm::cl::desc("Rewrite each finding in place: replace 'const T &' "
                 "with 'T '"),
  llvm::cl::cat(Cat));
static llvm::cl::opt<std::string> PathFilter(
  "path-filter",
  llvm::cl::desc("Only act on findings whose absolute path contains this "
                 "substring (matches anywhere). Default: act everywhere."),
  llvm::cl::cat(Cat));

/// Types that are "cheap to copy" per C++ Core Guidelines F.16, matched by
/// their fully-qualified record name (CXXRecordDecl::getQualifiedNameAsString()).
/// Using the qualified name avoids over-matching unrelated types that merely
/// share a simple name. To extend, add the fully-qualified canonical name --
/// e.g. `goto_programt::const_targett` resolves to the (libstdc++-specific)
/// `std::__cxx11::list<goto_programt::instructiont>::const_iterator`, not just
/// `const_iterator`; matching the simple name would flag every `const_iterator`
/// in the codebase, so extending the list to STL iterators is less trivial
/// than it looks.
static const std::set<std::string> CHEAP_TYPES = {
  // dstringt holds a single unsigned table index. irep_idt is a typedef
  // for dstringt; it lives in the global namespace, so its qualified name
  // is just "dstringt".
  "dstringt",
};

/// Return true if QT is one of the configured cheap-to-copy types.
static bool isCheapType(QualType QT)
{
  if(QT.isNull())
    return false;
  // Strip references and cv-qualifiers; we want the underlying record.
  if(QT->isReferenceType())
    QT = QT.getNonReferenceType();
  QT = QT.getLocalUnqualifiedType();
  // Resolve typedefs to the canonical record (e.g., irep_idt -> dstringt).
  const CXXRecordDecl *RD = QT->getAsCXXRecordDecl();
  if(!RD)
    return false;
  return CHEAP_TYPES.count(RD->getQualifiedNameAsString()) > 0;
}

/// Reconstruct a short signature snippet for the parameter, of the form
/// "const T &name", using the source spelling where possible (so users
/// see "const irep_idt &" rather than "const dstringt &").
static std::string spellingFor(
  const ParmVarDecl *PVD,
  const SourceManager &SM,
  const LangOptions &LO)
{
  SourceRange R = PVD->getSourceRange();
  if(R.isInvalid())
    return PVD->getType().getAsString() + " " + PVD->getNameAsString();
  CharSourceRange CSR = CharSourceRange::getTokenRange(R);
  StringRef Text = Lexer::getSourceText(CSR, SM, LO);
  // Collapse consecutive whitespace for readability of multi-line decls.
  std::string Out;
  Out.reserve(Text.size());
  bool PrevSpace = false;
  for(char c : Text)
  {
    if(c == '\n' || c == '\r' || c == '\t' || c == ' ')
    {
      if(!PrevSpace)
        Out.push_back(' ');
      PrevSpace = true;
    }
    else
    {
      Out.push_back(c);
      PrevSpace = false;
    }
  }
  return Out;
}

/// Walk through reference/qualified TypeLoc layers to reach the bare
/// type spelling (e.g., the `irep_idt` or `dstringt` token).
static TypeLoc innerTypeLoc(TypeLoc TL)
{
  while(true)
  {
    if(auto Ref = TL.getAs<ReferenceTypeLoc>())
    {
      TL = Ref.getPointeeLoc();
      continue;
    }
    if(auto Qual = TL.getAs<QualifiedTypeLoc>())
    {
      TL = Qual.getUnqualifiedLoc();
      continue;
    }
    break;
  }
  return TL;
}

class ParamCallback : public MatchFinder::MatchCallback
{
public:
  std::map<std::string, Replacements> *Replace = nullptr;

  void run(const MatchFinder::MatchResult &Result) override
  {
    const auto *PVD = Result.Nodes.getNodeAs<ParmVarDecl>("param");
    if(!PVD)
      return;

    const auto &SM = *Result.SourceManager;
    SourceLocation Loc = PVD->getLocation();
    if(Loc.isInvalid())
      return;

    // Skip parameters declared in system headers (e.g., libstdc++
    // template specialisations of std::less<irep_idt>): these are not
    // ours to fix and would create thousands of spurious findings.
    if(SM.isInSystemHeader(Loc))
      return;

    // We do *not* restrict to "main" files: most parameter declarations
    // live in headers (class definitions, function declarations), so we
    // need to follow #includes. Duplicates that arise from the same
    // header being parsed by many TUs are removed below via the Seen
    // set, keyed by (file, line, column).

    // The parameter type must be a const lvalue reference to one of our
    // cheap-to-copy types.
    QualType PT = PVD->getType();
    if(!PT->isLValueReferenceType())
      return;
    QualType Pointee = PT->getPointeeType();
    if(!Pointee.isConstQualified())
      return;
    if(!isCheapType(Pointee))
      return;

    // Skip parameters of special member functions whose signature is
    // dictated by the language: copy/move constructors and copy/move
    // assignment operators must take `const T &` (or `T &&`) and
    // returning by value would not compile.
    const auto *FD = dyn_cast<FunctionDecl>(PVD->getDeclContext());

    // Whether the parameter is one we are willing to rewrite in place.
    // Parameter names that appear inside function-type template
    // arguments (e.g. `std::function<void(const irep_idt &k)>`) have
    // their enclosing FunctionDecl in DeclContext but are NOT in that
    // FunctionDecl's getParamDecl() list. Rewriting them in isolation
    // desynchronises an in-class declaration from its out-of-class
    // definition, so we still flag them (so CI can catch any new
    // ones), but we don't auto-rewrite them.
    bool isFixable = false;
    if(FD)
    {
      for(unsigned i = 0; i < FD->getNumParams(); ++i)
      {
        if(FD->getParamDecl(i) == PVD)
        {
          isFixable = true;
          break;
        }
      }
    }

    if(FD)
    {
      if(const auto *CtorD = dyn_cast<CXXConstructorDecl>(FD))
      {
        if(CtorD->isCopyConstructor() || CtorD->isMoveConstructor())
          return;
      }
      if(const auto *MD = dyn_cast<CXXMethodDecl>(FD))
      {
        if(MD->isCopyAssignmentOperator() || MD->isMoveAssignmentOperator())
          return;
      }
      // Skip parameters of function template *instantiations*. We still
      // see the original template's parameters separately (and flag
      // those when the type is spelled as e.g. `const irep_idt &`); the
      // instantiations only pop up because Clang substituted a template
      // parameter to one of our cheap types, which is not something the
      // user can fix locally without changing the template signature
      // (and thereby pessimising other instantiations).
      if(FD->isTemplateInstantiation())
        return;
      // Same reasoning for member functions of class template
      // specialisations: the source-as-written signature may use a
      // template type parameter (e.g. `const keyT &`) that happens to
      // have been substituted to one of our cheap types.
      if(const auto *MD = dyn_cast<CXXMethodDecl>(FD))
      {
        if(isa<ClassTemplateSpecializationDecl>(MD->getParent()))
          return;
      }
    }

    // Skip if the parameter's source-as-written type is a (substituted)
    // template type parameter or otherwise dependent. Only flag when
    // the user actually wrote one of our cheap types, e.g.
    // `const irep_idt &x` or `const dstringt &x`. We walk the type
    // sugar chain rather than only inspecting the top-level type, so
    // that constructs like `const value_type &` -- where `value_type`
    // is a typedef whose substituted form is `dstringt` only because
    // the enclosing class template was instantiated with a cheap key
    // type -- are recognised and skipped.
    if(const TypeSourceInfo *TSI = PVD->getTypeSourceInfo())
    {
      QualType AsWritten = TSI->getType().getNonReferenceType();
      ASTContext &Ctx = *Result.Context;
      QualType Cur = AsWritten;
      while(!Cur.isNull())
      {
        const Type *T = Cur.getTypePtr();
        if(
          isa<SubstTemplateTypeParmType>(T) || isa<TemplateTypeParmType>(T) ||
          isa<SubstTemplateTypeParmPackType>(T) || isa<DependentNameType>(T))
          return;
        QualType Next = Cur.getSingleStepDesugaredType(Ctx);
        if(Next == Cur)
          break;
        Cur = Next;
      }
    }

    PresumedLoc PL = SM.getPresumedLoc(Loc);
    if(PL.isInvalid())
      return;

    // If --path-filter is set, drop findings whose file path doesn't
    // contain that substring (after path normalisation).
    if(!PathFilter.empty())
    {
      StringRef FN = PL.getFilename();
      if(FN.find(PathFilter) == StringRef::npos)
        return;
    }

    // Deduplicate: a single parameter declaration in source can match
    // multiple times via template instantiations. Keying by absolute
    // (file, line, column) collapses these to a single warning.
    Key K{PL.getFilename(), PL.getLine(), PL.getColumn()};
    if(!Seen.insert(K).second)
      return;

    std::string Spelling = spellingFor(PVD, SM, Result.Context->getLangOpts());

    // Build the entire diagnostic line in a string and emit it with a
    // single write, so that concurrent parallel runs do not interleave
    // partial lines on stdout.
    std::string Line;
    {
      llvm::raw_string_ostream OS(Line);
      OS << PL.getFilename() << ":" << PL.getLine() << ":" << PL.getColumn()
         << ": warning: parameter '" << PVD->getNameAsString() << "' has type '"
         << PT.getAsString()
         << "' which is cheap to copy; pass by value "
            "[cprover-pass-cheap-by-value]: "
         << Spelling << "\n";
    }
    llvm::outs() << Line;
    llvm::outs().flush();

    // In --fix mode, also queue an in-place replacement that rewrites
    // the parameter's type from `const T &` to `T `. We replace the
    // half-open character range from the start of the parameter
    // declaration (which covers the leading `const`) up to the start
    // of the parameter name, with `<spelled-T> `. This preserves the
    // user's choice of spelling (`irep_idt` vs. `dstringt`) and
    // absorbs any whitespace between `&` and the name.
    if(Replace == nullptr)
      return;
    // Only auto-rewrite parameters that are real method/function
    // parameters; see the isFixable comment above.
    if(!isFixable)
      return;
    const TypeSourceInfo *TSI = PVD->getTypeSourceInfo();
    if(!TSI)
      return;
    TypeLoc TL = TSI->getTypeLoc();
    SourceLocation Begin = PVD->getBeginLoc();
    SourceLocation End = PVD->getLocation();
    if(Begin.isInvalid() || End.isInvalid() || Begin == End)
      return;
    // Only safe to rewrite if both endpoints map to the same file, in
    // file (not macro-expansion) locations.
    Begin = SM.getFileLoc(Begin);
    End = SM.getFileLoc(End);
    if(SM.getFileID(Begin) != SM.getFileID(End))
      return;
    // Extract the spelled inner type so we preserve `irep_idt` vs.
    // `dstringt` exactly as the user wrote it.
    TypeLoc Inner = innerTypeLoc(TL);
    CharSourceRange InnerCSR =
      CharSourceRange::getTokenRange(Inner.getSourceRange());
    StringRef InnerText =
      Lexer::getSourceText(InnerCSR, SM, Result.Context->getLangOpts());
    if(InnerText.empty())
      return;
    std::string ReplaceText = InnerText.str();
    ReplaceText.push_back(' ');
    CharSourceRange Range = CharSourceRange::getCharRange(Begin, End);
    Replacement R(SM, Range, ReplaceText);
    std::string FilePath = std::string(R.getFilePath());
    if(FilePath.empty())
      return;
    if(auto Err = (*Replace)[FilePath].add(R))
    {
      llvm::errs() << "warning: failed to add replacement for " << FilePath
                   << ": " << llvm::toString(std::move(Err)) << "\n";
    }
  }

private:
  struct Key
  {
    std::string File;
    unsigned Line;
    unsigned Column;
    bool operator<(const Key &O) const
    {
      if(File != O.File)
        return File < O.File;
      if(Line != O.Line)
        return Line < O.Line;
      return Column < O.Column;
    }
  };
  std::set<Key> Seen;
};

int main(int argc, const char **argv)
{
  auto EP = CommonOptionsParser::create(argc, argv, Cat);
  if(!EP)
  {
    llvm::errs() << EP.takeError();
    return 1;
  }

  ParamCallback CB;
  MatchFinder Finder;
  Finder.addMatcher(parmVarDecl().bind("param"), &CB);

  if(Fix)
  {
    RefactoringTool Tool(EP->getCompilations(), EP->getSourcePathList());
    Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
      "-Wno-unknown-warning-option", ArgumentInsertPosition::BEGIN));
    CB.Replace = &Tool.getReplacements();
    int RC = Tool.run(newFrontendActionFactory(&Finder).get());
    // Manually apply replacements rather than using runAndSave: the
    // latter returns early when any TU has a parse error (e.g.,
    // optional solver back-ends with missing third-party headers),
    // and we still want fixes for the TUs that parsed cleanly.
    unsigned Saved = 0;
    for(auto &Entry : Tool.getReplacements())
    {
      const std::string &FilePath = Entry.first;
      const Replacements &Reps = Entry.second;
      auto Buffer = llvm::MemoryBuffer::getFile(FilePath);
      if(!Buffer)
      {
        llvm::errs() << "warning: could not read " << FilePath << ": "
                     << Buffer.getError().message() << "\n";
        continue;
      }
      llvm::Expected<std::string> NewContent =
        applyAllReplacements((*Buffer)->getBuffer(), Reps);
      if(!NewContent)
      {
        llvm::errs() << "warning: failed to apply replacements for " << FilePath
                     << ": " << llvm::toString(NewContent.takeError()) << "\n";
        continue;
      }
      std::error_code EC;
      llvm::raw_fd_ostream Out(FilePath, EC);
      if(EC)
      {
        llvm::errs() << "warning: could not write " << FilePath << ": "
                     << EC.message() << "\n";
        continue;
      }
      Out << *NewContent;
      ++Saved;
    }
    llvm::errs() << "Saved " << Saved << " files.\n";
    return RC;
  }
  else
  {
    ClangTool Tool(EP->getCompilations(), EP->getSourcePathList());
    Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
      "-Wno-unknown-warning-option", ArgumentInsertPosition::BEGIN));
    return Tool.run(newFrontendActionFactory(&Finder).get());
  }
}
