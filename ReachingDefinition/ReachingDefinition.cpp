#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <string>
#include <fstream>
#include <unordered_map>
#include <set>
#include <queue>

using namespace llvm;
using namespace std;

#define DEBUG_TYPE "ReachingDefinition"

namespace
{

struct ReachingDefinition : public FunctionPass
{
  static char ID;
  ReachingDefinition() : FunctionPass(ID) {}
  int InstructionIndex = 0;
  bool runOnFunction(Function &F) override
  {
    unordered_map<string, set<int>> ReachingVar_BB;
    unordered_map<string, map<int, string>> GEN_BB;
    unordered_map<string, map<int, string>> KILL_BB;
    unordered_map<string, map<int, string>> IN_BB;
    unordered_map<string, map<int, string>> OUT_BB;

    errs() <<"-------------------------------------------------------"<<"\n";
    errs() <<"                  Preliminary results:"<<"\n";
    errs() <<"-------------------------------------------------------"<<"\n";

    for (auto &basic_block : F) {
      std::string bbname = basic_block.getName().str();
      errs() << "\n----- " << bbname<<" -----  \n";
      set<string> generated_vars;

      int ist_count = InstructionIndex;
      map<int, string> gens = getGeneratedVariablesByIndex(&basic_block);
      InstructionIndex = ist_count;
      map<int, string> kills = getKilledVariablesByIndex(&basic_block);
    
      errs() << "GEN: ";
      GEN_BB[bbname] = gens;
      for (const auto &pair : gens) {
        errs() << pair.first << " " ;
      }
      
      if(bbname != "entry"){
        for (BasicBlock *pred : predecessors(&basic_block)) {
          string pred_bbname = pred->getName().str();
          for (const auto &pair : gens) {
            string varName = pair.second;
            bool found = false;
            int val;
            for (const auto &pair : GEN_BB[pred_bbname]) {
                if (pair.second == varName) {
                    found = true;
                    val = pair.first;
                    break;
                }
            }
            if (found) {
                kills[val] = varName;
            }
          }
      }
    }
      errs() << "\n" << "KILL: ";
      KILL_BB[bbname] = kills;
      for (const auto &pair : kills) {
        errs() << pair.first << " ";
      }
      OUT_BB[bbname] = gens; // Ins are initialised with Gens
      // INs are initialized as empty
      errs() << "\n" << "OUT: ";
      for (const auto &outerPair : OUT_BB[bbname]) {
        errs() << outerPair.first << " " ;
      }
      errs() << "\n";

    }
    
    bool change = true;
    unordered_map<string, map<int, string>> OLD_OUT_BB;
    while(change)
    {
      change = false;
      for(auto &basic_block : F)
      {
        std::string bbname = basic_block.getName().str();
        if(bbname != "entry")
        {
          OLD_OUT_BB[bbname] = OUT_BB[bbname];
          for (BasicBlock *pred : predecessors(&basic_block)) //IN_BB[bname] = union of OUT_pred[bbname]
          {
            string pred_bbname = pred->getName().str();
            
            
            IN_BB[bbname].insert(OUT_BB[pred_bbname].begin(), OUT_BB[pred_bbname].end()); 
            
          }   
          std::set<std::pair<int, std::string>> Difference;
          std::set<std::pair<int, std::string>> inSet(IN_BB[bbname].begin(), IN_BB[bbname].end());
          std::set<std::pair<int, std::string>> killSet(KILL_BB[bbname].begin(), KILL_BB[bbname].end());
          std::set_difference(inSet.begin(), inSet.end(),
                        killSet.begin(), killSet.end(),
                        std::inserter(Difference, Difference.end()));
          for (const auto &pair : Difference) {
            OUT_BB[bbname][pair.first] = pair.second;
          }
          if(OLD_OUT_BB[bbname] != OUT_BB[bbname])
          {
            change = true;
          }

        }
      }
    }
    errs() <<"-------------------------------------------------------"<<"\n";
    errs() <<"                     Final results:"<<"\n";
    errs() <<"-------------------------------------------------------"<<"\n";
    for (auto &basic_block : F) {
      std::string bbname = basic_block.getName().str();
      errs() << "\n----- " << bbname<<" ----- \n";
      errs() << "GEN: ";
      for (const auto &outerPair : GEN_BB[bbname]) {
        errs() << outerPair.first << " ";
      }
      errs() << "\n";
      errs() <<  "KILL: ";
      for (const auto &outerPair : KILL_BB[bbname]) {
        errs() << outerPair.first << " ";
      }
      errs() << "\n";
      errs() << "IN: ";
      for (const auto &outerPair : IN_BB[bbname]) {
        errs() <<outerPair.first << " ";
      }
      errs() << "\n";
      errs() << "OUT: ";
      for (const auto &outerPair : OUT_BB[bbname]) {
        errs() << outerPair.first << " ";
      }
      errs() << "\n";
     
    }

    return true;
  }



map<int, string> getGeneratedVariablesByIndex(BasicBlock *bb) {
    map<int, string>generatedVariablesMap;
    for (Instruction &instr : *bb) {
      ++InstructionIndex;
      if (isa<StoreInst>(instr)) {
          string varName = getVarFromInstruct(&instr); 
          bool found = false;
          int val;
          for (const auto &pair : generatedVariablesMap) {
              if (pair.second == varName) {
                  found = true;
                  val = pair.first;
                  break;
              }
          }
          if(found)
          {
            generatedVariablesMap.erase(val);
            generatedVariablesMap[InstructionIndex] = varName;
          }
          else
          {
            generatedVariablesMap[InstructionIndex] = varName;
          }
      }
    }
    return generatedVariablesMap;
}

  
map<int, string> getKilledVariablesByIndex(BasicBlock *bb) {
  map<int, string> generatedVariablesMap;
  map<int, string> killedVariables;
    for (Instruction &instr : *bb) {
      ++InstructionIndex;
      if (isa<StoreInst>(instr)) {
          string varName = getVarFromInstruct(&instr); 
          bool found = false;
          int val;
          for (const auto &pair : generatedVariablesMap) {
              if (pair.second == varName) {
                  found = true;
                  val = pair.first;
                  break;
              }
          }
          if(found)
          {
            auto it = generatedVariablesMap.find(val);
            if (it != generatedVariablesMap.end()) {
                killedVariables.insert(*it);

                generatedVariablesMap.erase(it);
            }
            generatedVariablesMap[InstructionIndex] = varName;
          }
          else
          {
            generatedVariablesMap[InstructionIndex] = varName;
          }
      }
    }
    return killedVariables;
}


  string getVarFromInstruct(Instruction *instruct) {
    string result;
    if (isa<LoadInst>(*instruct)) {
      LoadInst *loadInst = dyn_cast<LoadInst>(instruct);
      Value *useVal = loadInst->getPointerOperand();
      result = useVal->getName().str();
    }
    if (isa<StoreInst>(*instruct)) {
      StoreInst *storeInst = dyn_cast<StoreInst>(instruct);
      Value *defVal = storeInst->getPointerOperand();
      result = defVal->getName().str();
    }
    return result;
  }


}; // end of struct ReachingDefinition
} // end of anonymous namespace

char ReachingDefinition::ID = 0;
static RegisterPass<ReachingDefinition> X("ReachingDefinition", "Reaching Definition Pass",
                                      false /* Only looks at CFG */,
                                      true /* Analysis Pass */);
