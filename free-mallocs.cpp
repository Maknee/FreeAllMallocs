#include "llvm/ADT/SmallVector.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/DebugInfo/DIContext.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Pass.h"
#include "llvm/PassSupport.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ToolOutputFile.h"
#include <random>

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"


#include "command-line-options.h"
#include "llvm/IR/TypeBuilder.h"

using namespace llvm;

LLVMContext llvm_context;

Module *makeLLVMModule() {
  Module *mod = new Module("sum.ll", llvm_context);
  mod->setDataLayout("e-m:w-i64:64-f80:128-n8:16:32:64-S128");
  mod->setTargetTriple("x86_64-pc-windows-msvc19.15.26726");

  SmallVector<Type *, 2> function_args{
      IntegerType::getInt32Ty(mod->getContext()),
      IntegerType::getInt32Ty(mod->getContext())};

  FunctionType *function_type = FunctionType::get(
      IntegerType::getInt32Ty(mod->getContext()), function_args, false);

  Function *function =
      Function::Create(function_type, GlobalValue::ExternalLinkage, "add", mod);
  function->setCallingConv(CallingConv::C);

  Function::arg_iterator arg_begin = function->arg_begin();
  Value *v_a = arg_begin;
  v_a->setName("a");
  arg_begin++;
  Value *v_b = arg_begin;
  v_b->setName("b");

  BasicBlock *basic_block =
      BasicBlock::Create(mod->getContext(), "entry", function);

  AllocaInst *alloca_a_addr = new AllocaInst(
      IntegerType::getInt32Ty(mod->getContext()), 4, "a.addr", basic_block);
  alloca_a_addr->setAlignment(4);
  AllocaInst *alloca_b_addr = new AllocaInst(
      IntegerType::getInt32Ty(mod->getContext()), 4, "a.addr", basic_block);
  alloca_b_addr->setAlignment(4);

  StoreInst *st0 = new StoreInst(v_a, alloca_a_addr, false, basic_block);
  st0->setAlignment(4);
  StoreInst *st1 = new StoreInst(v_b, alloca_b_addr, false, basic_block);
  st1->setAlignment(4);

  LoadInst *ld0 = new LoadInst(alloca_a_addr, "", false, basic_block);
  ld0->setAlignment(4);
  LoadInst *ld1 = new LoadInst(alloca_b_addr, "", false, basic_block);
  ld1->setAlignment(4);

  BinaryOperator *binary_operator = BinaryOperator::Create(
      Instruction::BinaryOps::Add, ld0, ld1, "add", basic_block);
  ReturnInst::Create(mod->getContext(), binary_operator, basic_block);

  return mod;
}

struct BasicPass : public FunctionPass {
  static char ID;

  explicit BasicPass() : FunctionPass(ID) {}

  bool doInitialization(Module &module) override {
    if (GlobalVariable *global_variable =
            module.getGlobalVariable("llvm.global.annotations")) {
      for (Value *v_meta : global_variable->operands()) {
        if (ConstantArray *constant_array = dyn_cast<ConstantArray>(v_meta)) {
          for (Value *v_operands : constant_array->operands()) {
            if (ConstantStruct *constant_struct =
                    dyn_cast<ConstantStruct>(v_operands)) {
              if (constant_struct->getNumOperands() >= 2) {
                if (GlobalVariable *global_ann = dyn_cast<GlobalVariable>(
                        constant_struct->getOperand(1)->getOperand(0))) {
                  if (ConstantDataArray *constant_data_array =
                          dyn_cast<ConstantDataArray>(
                              global_ann->getOperand(0))) {
                    StringRef annotation = constant_data_array->getAsString();
                    if (annotation.startswith("stuff")) {
                      llvm::outs() << "GOT ITTTTTTTTT\n";
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    return true;
  }

  std::vector<Value*> global_variables_allocated;

  //structs
  class AllocationTree
  {
    std::set<Value*> children;
  };

  bool runOnFunction(Function &function) override {

    //memory allocation places
    //local variable
    //only way to know if freed is to check if
    //user free'd in this function
    //user free'd in different function
    //return pointer

    //if user freed in different function (rip), cause we wouldn't know if pass pointer is bueno
    //assume pass pointer is always valid

    //instead of looking for where to free, what about looking for places where the variable is not being used anymore
    //


    llvm::outs() << function.getName() << "\n==============\n";

    std::vector<AllocaInst*> local_variable_allocations;

    for (auto &basic_block : function) {
      for (Instruction& instruction : basic_block) {
        if(CallInst* call_inst = dyn_cast<CallInst>(&instruction))
        {
          //malloc calls
          if(call_inst->getCalledFunction()->getFunction().getName() == "malloc")
          {
            //find users until we store it into alloca
            std::function<AllocaInst*(Value*)> find_until_alloca;
            find_until_alloca = [&find_until_alloca](Value* val)
            {
              for(User* u : val->users())
              {
                if (AllocaInst *alloc_inst = dyn_cast<AllocaInst>(u)) {
                  return alloc_inst;
                }

                //if store, most likely alloca in its pointer_operand

                // %call4 = call noalias i8* @malloc(i64 16) #4
                // %7 = bitcast i8* %call4 to %struct.Stuff*
                // store %struct.Stuff* %7, %struct.Stuff** %s4, align 8

                if(StoreInst* store_inst = dyn_cast<StoreInst>(u))
                {
                  Value* pointer_operand = store_inst->getPointerOperand();
                  if (AllocaInst *alloc_inst = dyn_cast<AllocaInst>(pointer_operand)) {
                    return alloc_inst;
                  }
                }

                //uhhh maybe do it this way?
                // store into a GEP
                // %next = getelementptr inbounds %struct.List, %struct.List* %12, i32 0, i32 1

                // if(GetElementPtrInst* get_element_ptr_inst = dyn_cast<GetElementPtrInst>(u))
                // {
                //   get_element_ptr_inst->getPointerOperand();
                // }

                //else we loop until we find alloca
                return find_until_alloca(u);
              }
              return static_cast<AllocaInst*>(nullptr);
            };

            Value* original_alloca = find_until_alloca(call_inst);
            if(original_alloca)
            {
              outs() << "Alloca: " << *original_alloca << "\n";

              //is the element free'd
              bool is_free = false;
              
              //loop through all references to it and check where the memory is stopped being used
              std::function<void(Value*, int)> find_free;
              find_free = [&find_free, &original_alloca, &is_free](Value* value, int tabs)
              {
                //find all users
                for(User* u : value->users()) {
                  outs() << "used: " << std::string(tabs, '\t') << *u << "\n";

                  //check if store
                  //this is because we could have a GEP to the current struct and free sub elements
                  if(StoreInst* store_inst = dyn_cast<StoreInst>(u))
                  {
                    //make sure pointer operand isn't main struct's pointer
                    Value* pointer_operand = store_inst->getPointerOperand();
                    bool is_referencing_original_alloca = false;
                    for(Use& use : pointer_operand->uses()) {
                      Value* use_value = use.get();
                      
                      //do this check to make sure that we aren't checking the main struct's malloc again
                      if(use_value == original_alloca)
                      {
                        is_referencing_original_alloca = true;
                      }
                      //outs() << "compare: " << use_value << "|" << original_alloca << "\n";
                    }
                    //referencing original alloca (main struct)
                    if(is_referencing_original_alloca)
                    {
                      continue;
                    }

                    outs() << "Finding subelement malloc..." << std::string(tabs, '\t') << *pointer_operand << "\n";

                    Value* value_operand = store_inst->getValueOperand();

                    //need to check if this is malloc'ed
                    //TODO check subelement
                    std::function<Value*(Value*, int)> find_sub_element_malloc;
                    find_sub_element_malloc = [&find_sub_element_malloc](Value* value, int tabs)
                    {
                      for(User* u : value->users())
                      {
                        //if pointer, free
                        //return find_sub_element_malloc
                      }
                      return nullptr;
                    };
                    Value* sub_element_malloc = find_sub_element_malloc(value_operand, tabs + 1);
                    if(sub_element_malloc)
                    {
                      //keep track and free if possible
                    }
                  }

                  if(CallInst* call_to_function = dyn_cast<CallInst>(u))
                  {
                    Function* called_function = call_to_function->getCalledFunction();
                    //this is a free to this alloca (OKAY, we are good)
                    if(called_function->getName() == "free")
                    {
                      is_free = true;
                      return;
                    } 
                    else 
                    {
                      //this is a call to other function...
                      //TODO check call in other function
                      std::function<bool(Value*)> find_free_in_other_function;
                      find_free_in_other_function = [](Value* value)
                      {
                        return false;
                      };

                      for(Argument& arg : called_function->args())
                      {
                        outs() << "YEAH: " << arg << "\n";

                        //if free is found, OKAY
                        if(find_free_in_other_function(&arg))
                        {
                          is_free = true;
                        }
                      }

                    }
                  }

                  find_free(u, tabs + 1);
                }                
              };
              find_free(original_alloca, 1);

              //free the last usage of variable and assume not in conditional case!
              //TODO: condition case
              if (!is_free)
              {
                  //last element we found related to the variable!
                  Value *last_element = original_alloca;
                  while(!last_element->user_empty())
                  {
                    //this is actually the first element... in the source
                    last_element = last_element->user_back();
                    
                  }

                  //create a free
                  if(Instruction* last_instruction = dyn_cast<Instruction>(last_element))
                  {
                    IRBuilder<> ir_builder(last_instruction->getNextNode());

                    //check if free is avaliable
                    const auto &mod = last_instruction->getModule();
                    Function *free_function = mod->getFunction("free");
                    if(free_function)
                    {
                      free_function->dump();
                      for(Argument& arg : free_function->args())
                      {
                        errs() << arg << "\n";
                        errs() << *arg.getType() << "\n";
                      }

                      LoadInst* loaded_alloca = ir_builder.CreateLoad(original_alloca);

                      //check if we can cast
                      if(loaded_alloca->getType()->canLosslesslyBitCastTo(IntegerType::getInt8PtrTy(mod->getContext()))) {
                        //cast
                        Value* bit_cast = ir_builder.CreateBitOrPointerCast(loaded_alloca, IntegerType::getInt8PtrTy(mod->getContext()));

                        //arguments
                        const std::vector<Value*> arguments{ bit_cast };
                        
                        //make call
                        ir_builder.CreateCall(free_function, arguments);
                      }
                    }
                    else
                    {
                      errs() << "free function not found!" << "\n";
                      exit(-1);
                    }
                  }
              }
            }
          }
          outs() << call_inst->getFunction()->getName() << " -> " << call_inst->getCalledFunction()->getName() << "\n";

        }
      }
    }
    
    return true;
  }
};

char BasicPass::ID = 0;

static RegisterPass<BasicPass> register_pass("free-mallocs",
                                             "basic memory tracer");

// register pass for clang use
void registerMyPassPass(const PassManagerBuilder & a, legacy::PassManagerBase &PM) {
  PM.add(new BasicPass());
}

static RegisterStandardPasses RegisterMBAPass(PassManagerBuilder::EP_EarlyAsPossible, registerMyPassPass);
