// Detect irept copy-then-modify patterns that could use std::move.
//
// Build:
//   clang++-18 -o check-irep-moves scripts/check_irep_moves.cpp \
//     $(llvm-config-18 --cxxflags | sed 's/-Werror//g') \
//     -L/usr/lib/llvm-18/lib -lclang-cpp \
//     $(llvm-config-18 --ldflags --libs --system-libs) -fno-rtti
//
// Usage:
//   ./check-irep-moves -p build/compile_commands.json src/goto-symex/*.cpp

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"

using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::tooling;

static llvm::cl::OptionCategory Cat("check-irep-moves");
static llvm::cl::opt<bool>
  Debug("debug", llvm::cl::desc("Debug output"), llvm::cl::cat(Cat));

static bool inheritsFromIrep(const CXXRecordDecl *RD, int depth = 0)
{
  if(!RD || depth > 10)
    return false;
  auto name = RD->getNameAsString();
  if(name == "irept" || name == "sharing_treet")
    return true;
  // Try definition
  const auto *Def = RD->getDefinition();
  if(!Def)
    return false;
  for(const auto &Base : Def->bases())
  {
    auto BT = Base.getType();
    // Handle template specializations
    if(const auto *TST = BT->getAs<TemplateSpecializationType>())
    {
      if(auto *TD = TST->getTemplateName().getAsTemplateDecl())
        if(auto *TRD = dyn_cast<CXXRecordDecl>(TD->getTemplatedDecl()))
          if(inheritsFromIrep(TRD, depth + 1))
            return true;
    }
    if(const auto *BRD = BT->getAsCXXRecordDecl())
      if(inheritsFromIrep(BRD, depth + 1))
        return true;
  }
  return false;
}

class PostCopyRefFinder : public RecursiveASTVisitor<PostCopyRefFinder>
{
public:
  const VarDecl *Target;
  SourceLocation After;
  const SourceManager &SM;
  bool Found = false;

  PostCopyRefFinder(const VarDecl *T, SourceLocation A, const SourceManager &S)
    : Target(T), After(A), SM(S)
  {
  }

  bool VisitDeclRefExpr(DeclRefExpr *DRE)
  {
    if(
      DRE->getDecl() == Target &&
      SM.isBeforeInTranslationUnit(After, DRE->getBeginLoc()))
    {
      Found = true;
      return false;
    }
    return true;
  }
};

/// Check if a variable is ever modified (non-const method call, assignment, etc.)
/// Conservative: assumes mutable if we can't prove const.
class MutableUseChecker : public RecursiveASTVisitor<MutableUseChecker>
{
public:
  const VarDecl *Target;
  bool HasMutableUse = false;

  MutableUseChecker(const VarDecl *T) : Target(T)
  {
  }

  bool VisitCXXMemberCallExpr(CXXMemberCallExpr *MCE)
  {
    // Check if this is a non-const method call on our variable
    if(const auto *ObjExpr = MCE->getImplicitObjectArgument())
    {
      if(const auto *DRE = dyn_cast<DeclRefExpr>(ObjExpr->IgnoreImplicit()))
      {
        if(DRE->getDecl() == Target)
        {
          if(const auto *MD = MCE->getMethodDecl())
          {
            if(!MD->isConst())
            {
              HasMutableUse = true;
              return false;
            }
          }
          else
          {
            HasMutableUse = true; // can't determine, assume mutable
            return false;
          }
        }
      }
    }
    return true;
  }

  bool VisitBinaryOperator(BinaryOperator *BO)
  {
    if(BO->isAssignmentOp())
    {
      if(
        const auto *DRE = dyn_cast<DeclRefExpr>(BO->getLHS()->IgnoreImplicit()))
      {
        if(DRE->getDecl() == Target)
        {
          HasMutableUse = true;
          return false;
        }
      }
    }
    return true;
  }

  bool VisitUnaryOperator(UnaryOperator *UO)
  {
    if(UO->getOpcode() == UO_AddrOf)
    {
      if(
        const auto *DRE =
          dyn_cast<DeclRefExpr>(UO->getSubExpr()->IgnoreImplicit()))
      {
        if(DRE->getDecl() == Target)
        {
          HasMutableUse = true;
          return false;
        }
      }
    }
    return true;
  }

  bool VisitCallExpr(CallExpr *CE)
  {
    // Check if our variable is passed as a non-const reference argument
    if(const auto *Callee = CE->getDirectCallee())
    {
      for(unsigned i = 0; i < CE->getNumArgs() && i < Callee->getNumParams();
          ++i)
      {
        if(
          const auto *DRE =
            dyn_cast<DeclRefExpr>(CE->getArg(i)->IgnoreImplicit()))
        {
          if(DRE->getDecl() == Target)
          {
            QualType PT = Callee->getParamDecl(i)->getType();
            if(
              PT->isReferenceType() && !PT->getPointeeType().isConstQualified())
            {
              HasMutableUse = true;
              return false;
            }
          }
        }
      }
    }
    else
    {
      // Can't resolve callee — check if any arg is our variable
      for(unsigned i = 0; i < CE->getNumArgs(); ++i)
      {
        if(
          const auto *DRE =
            dyn_cast<DeclRefExpr>(CE->getArg(i)->IgnoreImplicit()))
        {
          if(DRE->getDecl() == Target)
          {
            HasMutableUse = true; // conservative
            return false;
          }
        }
      }
    }
    return true;
  }
};

class Callback : public MatchFinder::MatchCallback
{
public:
  void run(const MatchFinder::MatchResult &Result) override
  {
    const auto *VD = Result.Nodes.getNodeAs<VarDecl>("var");
    if(!VD)
      return;

    const auto &SM = *Result.SourceManager;
    if(!SM.isInMainFile(VD->getLocation()))
      return;
    if(VD->getType().isConstQualified())
      return;

    const auto *RD = VD->getType()->getAsCXXRecordDecl();
    bool isIrep = inheritsFromIrep(RD);

    if(Debug && RD)
    {
      llvm::errs() << "  " << SM.getSpellingLineNumber(VD->getLocation())
                   << ": " << VD->getNameAsString()
                   << " type=" << RD->getNameAsString() << " irep=" << isIrep
                   << "\n";
    }

    if(!isIrep)
      return;

    // Check: copy that's never modified (should be const ref)
    checkUnmodifiedCopy(VD, Result);

    // Get initializer, unwrap to find the source
    const Expr *Init = VD->getInit();
    if(!Init)
      return;
    Init = Init->IgnoreImplicit();

    // Must be copy construction
    if(const auto *CE = dyn_cast<CXXConstructExpr>(Init))
    {
      if(CE->getNumArgs() != 1)
        return;
      auto *Ctor = CE->getConstructor();
      if(Ctor && Ctor->isMoveConstructor())
        return;
      // Restrict to a genuine same-type copy. A converting constructor such
      // as address_of_exprt(const exprt &) or code_typet::parametert(const
      // typet &) takes its argument by a const lvalue reference, so the
      // rvalue produced by std::move would simply bind to that const
      // reference and the underlying copy would still happen -- std::move
      // there is a no-op. (And a non-irept conversion like
      // unsignedbv_typet(size_t) duplicates no irept storage at all.) For a
      // genuine same-type copy the move constructor exists, so suggesting
      // std::move does avoid the copy.
      if(Ctor && !Ctor->isCopyConstructor())
        return;
      Init = CE->getArg(0)->IgnoreImplicit();
    }
    else
      return;

    // Source must be a named variable
    const auto *SrcRef = dyn_cast<DeclRefExpr>(Init);
    if(!SrcRef)
      return;
    const auto *SrcVD = dyn_cast<VarDecl>(SrcRef->getDecl());
    if(!SrcVD || isa<ParmVarDecl>(SrcVD))
      return;
    {
      // Skip const sources: `std::move` of a const value silently
      // copy-constructs (the rvalue has type `const T&&` which binds
      // to the copy constructor) and would in any case be unsafe for
      // a `const auto &` alias into someone else's data.  The check
      // needs to look through references, since for `const auto &x`
      // the variable's top-level type is a reference and is not
      // itself const-qualified.
      QualType SrcQT = SrcVD->getType();
      if(SrcQT->isReferenceType())
        SrcQT = SrcQT.getNonReferenceType();
      if(SrcQT.isConstQualified())
        return;
    }

    // Check source not used after copy
    const auto *FD = dyn_cast_or_null<FunctionDecl>(VD->getDeclContext());
    if(!FD || !FD->getBody())
      return;

    PostCopyRefFinder Finder(SrcVD, VD->getEndLoc(), SM);
    Finder.TraverseStmt(const_cast<Stmt *>(FD->getBody()));
    if(Finder.Found)
      return;

    // Skip loop-reused sources: if `VD` is inside a loop body and
    // `SrcVD` is declared outside that loop, then the loop will copy
    // from `SrcVD` once per iteration; converting that copy to a move
    // would leave a moved-from `SrcVD` for every subsequent iteration.
    {
      ASTContext &Ctx = *Result.Context;
      const Stmt *EnclosingLoop = nullptr;
      DynTypedNode Cur = DynTypedNode::create(*VD);
      while(EnclosingLoop == nullptr)
      {
        const auto Parents = Ctx.getParents(Cur);
        if(Parents.empty())
          break;
        Cur = Parents[0];
        if(const auto *S = Cur.get<Stmt>())
        {
          if(
            isa<ForStmt>(S) || isa<WhileStmt>(S) || isa<DoStmt>(S) ||
            isa<CXXForRangeStmt>(S))
          {
            EnclosingLoop = S;
            break;
          }
        }
      }
      if(
        EnclosingLoop && SM.isBeforeInTranslationUnit(
                           SrcVD->getBeginLoc(), EnclosingLoop->getBeginLoc()))
        return;
    }

    llvm::errs() << SM.getFilename(VD->getLocation()) << ":"
                 << SM.getSpellingLineNumber(VD->getLocation())
                 << ": warning: '" << VD->getNameAsString() << "' copies '"
                 << SrcVD->getNameAsString() << "' (type "
                 << VD->getType().getAsString()
                 << ") which is not used afterwards; "
                 << "use std::move [cprover-unnecessary-irep-copy]\n";
  }

  void
  checkUnmodifiedCopy(const VarDecl *VD, const MatchFinder::MatchResult &Result)
  {
    const auto &SM = *Result.SourceManager;
    if(!SM.isInMainFile(VD->getLocation()))
      return;
    if(VD->getType().isConstQualified() || VD->getType()->isReferenceType())
      return;
    const auto *RD = VD->getType()->getAsCXXRecordDecl();
    if(!inheritsFromIrep(RD))
      return;
    const Expr *Init = VD->getInit();
    if(!Init)
      return;
    Init = Init->IgnoreImplicit();
    if(const auto *CE = dyn_cast<CXXConstructExpr>(Init))
    {
      if(CE->getNumArgs() != 1)
        return;
      auto *Ctor = CE->getConstructor();
      if(!Ctor || Ctor->isMoveConstructor())
        return;
    }
    else
      return;
    // Check if the source is a temporary (function return, constructor call).
    // A const reference to a temporary would dangle.
    const Expr *Src = Init;
    if(const auto *CE = dyn_cast<CXXConstructExpr>(Src))
    {
      if(CE->getNumArgs() == 1)
        Src = CE->getArg(0)->IgnoreImplicit();
    }
    // If source is NOT a DeclRefExpr or MemberExpr, it's likely a temporary
    if(!isa<DeclRefExpr>(Src) && !isa<MemberExpr>(Src))
      return;
    // Skip MemberExpr sources: the existing MutableUseChecker only
    // tracks mutations of the destination VarDecl, so it cannot detect
    // a `this->member = ...` between the copy and a later use of VD.
    // Suggesting `const auto &` would alias to the post-mutation value
    // -- not the snapshot the user intended.
    if(isa<MemberExpr>(Src))
      return;
    // Skip reference-typed sources: a `T &alias` is often introduced
    // precisely because the referee will be mutated, and a `const T &`
    // copy would observe the post-mutation value rather than the
    // snapshot the caller wants.  We can't tell without flow analysis
    // whether that's the case here, so play it safe.
    if(const auto *DRE = dyn_cast<DeclRefExpr>(Src))
    {
      if(const auto *SrcVD = dyn_cast<VarDecl>(DRE->getDecl()))
      {
        if(SrcVD->getType()->isReferenceType())
          return;
      }
    }
    // Source type must match variable type (otherwise it's a conversion)
    if(Src->getType().getCanonicalType() != VD->getType().getCanonicalType())
      return;
    // If source is a MemberExpr calling a method that returns by value,
    // a const ref would dangle
    if(const auto *ME = dyn_cast<MemberExpr>(Src))
    {
      (void)ME; // MemberExpr accessing a field is fine (returns lvalue ref)
    }

    const auto *FD = dyn_cast_or_null<FunctionDecl>(VD->getDeclContext());
    if(!FD || !FD->getBody())
      return;
    MutableUseChecker Checker(VD);
    Checker.TraverseStmt(const_cast<Stmt *>(FD->getBody()));
    if(!Checker.HasMutableUse)
    {
      llvm::errs() << SM.getFilename(VD->getLocation()) << ":"
                   << SM.getSpellingLineNumber(VD->getLocation())
                   << ": warning: '" << VD->getNameAsString() << "' (type "
                   << VD->getType().getAsString()
                   << ") is copy-initialized but never modified; "
                   << "use const reference [cprover-unmodified-irep-copy]\n";
    }
  }
};

int main(int argc, const char **argv)
{
  auto EP = CommonOptionsParser::create(argc, argv, Cat);
  if(!EP)
  {
    llvm::errs() << EP.takeError();
    return 1;
  }
  ClangTool Tool(EP->getCompilations(), EP->getSourcePathList());
  Tool.appendArgumentsAdjuster(getInsertArgumentAdjuster(
    "-Wno-unknown-warning-option", ArgumentInsertPosition::BEGIN));

  Callback CB;
  MatchFinder Finder;
  Finder.addMatcher(
    varDecl(hasLocalStorage(), hasInitializer(anything())).bind("var"), &CB);
  return Tool.run(newFrontendActionFactory(&Finder).get());
}
