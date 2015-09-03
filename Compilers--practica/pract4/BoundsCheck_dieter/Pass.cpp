#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/Pass.h>
#include <llvm/Support/Debug.h>

#include <list>

#define DEBUG_TYPE "cheetah::boundscheck"

using namespace llvm;

namespace {
struct BoundsCheck : public FunctionPass {
private:
  IRBuilder<> *Builder;
  Function *Assert = nullptr;

public:
  static char ID;
  BoundsCheck() : FunctionPass(ID) {
    Builder = new IRBuilder<>(getGlobalContext());
  }

  /// Entry point of the pass; this function performs the actual analysis or
  /// transformation, and is called for each function in the module.
  ///
  /// The returned boolean should be `true` if the function was modified,
  /// `false` if it wasn't.
  bool runOnFunction(Function &F) override {
    DEBUG({
      dbgs() << "BoundsCheck: processing function '";
      dbgs().write_escaped(F.getName()) << "'\n";
    });

    // Instantiate the assert function once per module
    if (Assert == nullptr || Assert->getParent() != F.getParent())
      Assert = getAssertFunction(F.getParent());

    // Find all GEP instructions
    // NOTE: we need to do this first, because the iterators get invalidated
    //       when modifying underlying structures
    std::list<GetElementPtrInst *> WorkList;
    for (auto &FI : F)
    {  // Iterate function -> basic blocks
       for (auto &BI : FI)
       { 	// Iterate basic block -> instructions
          if (auto *GEP = dyn_cast<GetElementPtrInst>(&BI))
          {
             WorkList.push_back(GEP);
        	}
      	}
    }

    // Process any GEP instructions
    bool Changed = false;
    for (GetElementPtrInst *GEP : WorkList) 
    {
      // DEBUG(dbgs() << "GEP : " << *GEP << "\n");
      // Operands of the GEP
	    Value* array = GEP->getOperand(0);
	    Value* two = GEP->getOperand(1);
	    Value* index = GEP->getOperand(2);
    
      // The index of the array call is a constant number, for example a[10]
      if(ConstantInt* CI = dyn_cast<ConstantInt>(index))
      {          
         APInt index_constant = CI->getValue();

         // The index of the array call is negative and as such is always out of bounds.
         if(index_constant.isNegative())
         {
            report_fatal_error("Negative index call found! \n");  // TODO more specific reporting?
            return false;
         }

         uint64_t arraysize = (ALOC->getAllocatedType())->getArrayNumElements();
         
         // The index of the array call is bigger than the allocated size of the array
         if(arraysize <= index_constant)
         {
            report_fatal_error("Static out of bounds array call found! \n");
            return false;
         }
      }

    return Changed;
  }

private:
  ///
  /// This function displays a failed assertion, together with the source
  /// location (file name and line number). Afterwards, it abort()s the program.
  Function *getAssertFunction(Module *Mod) {
    Type *CharPtrTy = Type::getInt8PtrTy(getGlobalContext());
    Type *IntTy = Type::getInt32Ty(getGlobalContext());
    Type *VoidTy = Type::getVoidTy(getGlobalContext());

    std::vector<Type *> assert_arg_types;
    assert_arg_types.push_back(CharPtrTy); // const char *__assertion
    assert_arg_types.push_back(CharPtrTy); // const char *__file
    assert_arg_types.push_back(IntTy);     // int __line

    FunctionType *assert_type =
        FunctionType::get(VoidTy, assert_arg_types, true);

    Function *F = Function::Create(assert_type, Function::ExternalLinkage,
                                   Twine("__assert"), Mod);
    F->addFnAttr(Attribute::NoReturn);
    F->setCallingConv(CallingConv::C);
    return F;
  }
};
}

char BoundsCheck::ID = 0;
static RegisterPass<BoundsCheck> X("cheetah-boundscheck",
                                   "Cheetah Bounds Check Pass", false, false);
