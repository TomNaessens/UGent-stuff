#include <llvm/IR/DebugInfo.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/Pass.h>
#include <llvm/Support/Debug.h>

// Include BasicBlockUtils for SplitBlockAndInsertIfThen
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

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
      {   // Iterate basic block -> instructions
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
      Value* Array = GEP->getOperand(0);
      Value* Index = GEP->getOperand(2);

      // Set some variables to be able to retrieve the filename and linenumber
      MDNode *N = GEP->getMetadata("dbg");
      DILocation loc(N);

      // Define the debugging the parameters
      std::string AssertMessageString = "Array out of bounds detected.";
      std::string FilenameString = loc.getFilename();
      uint32_t LineNumberInt = loc.getLineNumber();

      // The index of the array call is a constant number, for example a[10]
      if(ConstantInt* CI = dyn_cast<ConstantInt>(Index))
      {
        APInt IndexConstant = CI->getValue();

        // The index of the array call is negative and as such is always out of bounds.
        if(IndexConstant.isNegative())
        {
          report_fatal_error(AssertMessageString + " Tried to retrieve a negative index ("
                             + std::to_string(IndexConstant.getSExtValue())
                             + ") in " + FilenameString
                             + ":" + std::to_string(LineNumberInt));
        }

        if(AllocaInst* ALOC = dyn_cast<AllocaInst>(Array))
        {
          uint64_t ArraySize = ALOC->getAllocatedType()->getArrayNumElements();

          // The index of the array call is bigger than the allocated size of the array
          if(ArraySize <= IndexConstant.getLimitedValue())
          {
            report_fatal_error(AssertMessageString + " Tried to retrieve with index "
                               + std::to_string(IndexConstant.getSExtValue())
                               + " while the array only contains "
                               + std::to_string(ArraySize)
                               + " entries in " + FilenameString
                               + ":" + std::to_string(LineNumberInt));
          }
        }
      // The index of the array call is a loadinstruction, for example a[n]
      } else if(dyn_cast<LoadInst>(Index)) {
        // We can't know which value is in the variable at compile time,
        // so we have to find out a way to check this at runtime. Herefore,
        // we have to insert some code before the getelementptr call

        // Set Changed to true as the function was changed
        Changed = true;

        // Are we out of bounds? Get the variables and sizes
        AllocaInst* ALOC = dyn_cast<AllocaInst>(Array);
        uint64_t ArraySizeUInt = ALOC->getAllocatedType()->getArrayNumElements();
        Value* ArraySize = Builder->getInt32(ArraySizeUInt);

        // Set the builder to the above the termination instruction
        Builder->SetInsertPoint(GEP);

        // Create an less or equal equation
        Value* InBoundsCond = Builder->CreateICmpSLE(ArraySize, Index, "isoutofbounds");
        // Check if the index is positive
        Value* IsPositiveCond = Builder->CreateICmpSLT(Index, Builder->getInt32(0), "isnegative");
        // Or the last two conditions
        Value* ThrowAssertCond = Builder->CreateOr(InBoundsCond, IsPositiveCond, "throwassert");

        // SplitBlockAndInsertIfThen is a nice function we can use!
        // It adds a if-then block above a given Instruction
        // and returns the termination term, so we can build our block above it
        // see http://llvm.org/docs/doxygen/html/namespacellvm.html#a346d45cf9468c1e9912f869725442575

        // Create branch weights to aid the branchpredictor a bit
        MDBuilder MB(getGlobalContext());
        MDNode* BranchWeights = MB.createBranchWeights(1, 10000000);

        TerminatorInst* TI = SplitBlockAndInsertIfThen(
            ThrowAssertCond,  // Value* Cond
            GEP,              // Instruction* SplitBefore
            true,             // bool Unreachable
            BranchWeights     // MDNode* BranchWeights
        );

        // Set the builder to the above the termination instruction
        Builder->SetInsertPoint(TI);

        // Convert the debugging messages to Value*s
        Value* AssertMessage = Builder->CreateGlobalStringPtr(AssertMessageString, "__assertion");
        Value* Filename = Builder->CreateGlobalStringPtr(FilenameString, "__file");
        Value* LineNumber =  Builder->getInt32(LineNumberInt);

        // Create the call to the assertion function
        Builder->CreateCall3(Assert,        // Function
                             AssertMessage, // AssertMessage
                             Filename,      // Filename
                             LineNumber     // LineNumber
        );
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
