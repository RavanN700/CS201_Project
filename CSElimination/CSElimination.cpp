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
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include <string>
#include <fstream>
#include <unordered_map>
#include <map>
#include <vector>
#include <set>
#include <queue>
#include <string.h>
#include <sstream>
using namespace llvm;
using namespace std;

#define DEBUG_TYPE "CSElimination"

namespace
{
  /// @brief 
  map <string, set<string>> dominator_map;
  map <string, int> block_levels;
  map <string, vector<int>> available_exp_levels;
  struct CSElimination: public FunctionPass
  {
    static char ID;
    CSElimination(): FunctionPass(ID) {}
    

    bool runOnFunction(Function & F) override
    {
       

      unordered_map<string, set < string>> availExpressionsBB;
      unordered_map<string, set < string>> gensBB;
      unordered_map<string, set < string>> killsBB;
      unordered_map<string, set < string>> OutsBB;
      unordered_map<string, set < string>> InsBB;
      //errs() << "AvailExpression: ";
      //errs() << F.getName() << "\n";

      //Iterating through the entire CFG and finding all the expressions computed.
      set<vector < string>> allExpressionsVec;
      int InstructionIndex = 1;
      for (auto &basic_block: F)
      {
        string bbname = basic_block.getName().str();
        //errs() << bbname << "\n";
        for (Instruction &instruct: basic_block)
        { 
          //errs() << instruct << "\n";
          if (isa<BinaryOperator> (instruct))
          {
            
            allExpressionsVec.insert(getExpressionFromInstruct(&instruct));
          }
        }
      }
      

      set<string> allExpressions = getSetFromVec(allExpressionsVec);
      //Computing Gens and Kills and initialization step
      for (auto &basic_block: F)
      {
        //Getting the generated expressions for a basic block
        string bbname = basic_block.getName().str();
        set<string> generatedExpressions = getGeneratedExpressions(&basic_block);
        
        gensBB[bbname] = generatedExpressions;

        
        set<string> killedExpressions = getKilledExpressions(&basic_block, allExpressionsVec);
        killsBB[bbname] = killedExpressions;
        
        //start node initialisation
        if (predecessors(&basic_block).empty())
        {
          OutsBB[bbname] = generatedExpressions;
        }
        else
        {
          OutsBB[bbname] = allExpressions;
        }
      }

  


      //Iterative algorithm to compute Available expressions
      unordered_map<string, set < string>> oldOuts;
      unordered_map<string, bool> exitCondition;
      bool changed = false;
      do {  changed = true;
        set<string> intersectionSet, tempSet;
        for (auto &basic_block: F)
        {
          string bbname = basic_block.getName().str();
          if (predecessors(&basic_block).empty())
            continue;
          oldOuts[bbname] = OutsBB[bbname];
          intersectionSet.clear();
          for (BasicBlock *pred: predecessors(&basic_block))
          {
            string predName = pred->getName().str();
            if (intersectionSet.empty())
            {
              intersectionSet = OutsBB[predName];
            }
            else
            {
              tempSet.clear();
              set_intersection(intersectionSet.begin(), intersectionSet.end(), OutsBB[predName].begin(), OutsBB[predName].end(), inserter(tempSet, tempSet.begin()));
              intersectionSet.clear();
              intersectionSet = tempSet;
            }
          }

          set<string> disjointSet;

          std::set_difference(intersectionSet.begin(), intersectionSet.end(),
            killsBB[bbname].begin(), killsBB[bbname].end(),
            inserter(disjointSet, disjointSet.end()));
          disjointSet.insert(gensBB[bbname].begin(), gensBB[bbname].end());
          OutsBB[bbname] = disjointSet;
          if (OutsBB[bbname] == oldOuts[bbname])
          {
            exitCondition[bbname] = true;
          }
          else
          {
            exitCondition[bbname] = false;
          }
        }

        //method to check if all blocks have reached exit condition, if all have remained unchanged then this will help exit the do-while loop
        for (const auto &element: exitCondition)
        {
          changed = changed && element.second;
        }
      } while (!changed);
      //Printing the final result of all Outs
      for (auto &basic_block: F)
      {
        std::string bbname = basic_block.getName().str();
        //errs() << bbname << " : ";
        //printSet(OutsBB[bbname]);
      }

      

      
      set<string> basic_blocks;
      dominator_map["entry"].insert("entry");
      /*
      for (auto &basic_block: F)
      {
        string bbname = basic_block.getName().str();
        basic_blocks.insert(bbname);
      }
      for(const auto& str :basic_blocks)
      {
        if(str!="entry")
        {
          dominator_map[str] = basic_blocks;
        }
      }
      

      for(auto &basic_block: F)
      {
        string bbname = basic_block.getName().str();
        vector<string> predecessor_list;
        set<string> result;
        if(bbname != "entry")
        {
        for(BasicBlock *pred: predecessors(&basic_block))
        {
          string predname = pred->getName().str();
          predecessor_list.push_back(predname);
        }
        result = dominator_map[predecessor_list[0]];

        for(int i=0; i<predecessor_list.size();i++)
        {
          set<string> temp;
          set_intersection(
            result.begin(), result.end(),
            dominator_map[predecessor_list[i]].begin(), dominator_map[predecessor_list[i]].end(),
            inserter(temp, temp.begin()));
          result = move(temp);
         
        }
        set<string> temp;
        set<string> own;
        own.insert(bbname);
        set_union(
          result.begin(), result.end(),
          own.begin(), own.end(),
          inserter(temp, temp.begin())
        );

        result = move(temp);

        dominator_map[bbname] = result;
        }

      }
      */
     
     for(auto &basic_block : F)
     {
        string bbname = basic_block.getName().str();
        
        if (bbname == "entry")
        {
          block_levels[bbname] = 1;
        }
        else{
          block_levels[bbname] = INT_MAX;
        }
     }

     for(auto&basic_block : F)
     {
      string bbname = basic_block.getName().str();

        if(bbname != "entry")
        {
          int min = INT_MAX - 1;
          for(BasicBlock* pred : predecessors(&basic_block))
          {
            string predname = pred->getName().str();
            if(min >= block_levels[predname])
            {
              min = block_levels[predname];
            }
          }
          block_levels[bbname] = min+1;
        }
     }

       
      

      
      for(auto &pair : OutsBB)
      {
        for(auto& basic_block : F)
        {
          string bbname = basic_block.getName().str();
          //errs() << pair.first << "\n";
          if(bbname.compare(pair.first) != 0)
            continue;

            vector<string> exps;

          for(auto&exp: pair.second)
          {
            //errs() << exp << "\n";
            bool found = false;
            
            for(Instruction&instruct : basic_block)
            {
              if(isa<BinaryOperator> (instruct))
              {
                
                string exp_vec = getExpressionFromInstruct(&instruct)[2];
                if(exp_vec.compare(exp) == 0)
                  found = true;
              }
            }
            if(!found)
              exps.push_back(exp);
          }
         
          for(int i=0; i<exps.size(); i++)
          {
            pair.second.erase(exps[i]);
          }
          


        }
      }



      for(const auto & pair : OutsBB)
      {
        for(auto &element : pair.second)
        {
          available_exp_levels[element].push_back(block_levels[pair.first]);
        }
      }
      vector <string> deleted_expressions;
      for(const auto & pair : available_exp_levels)
      {
        if(pair.second.size() < 2)
          deleted_expressions.push_back(pair.first);
      } 
      for(int i=0; i<deleted_expressions.size(); i++)
      {
        available_exp_levels.erase(deleted_expressions[i]);
      }
      if(available_exp_levels.empty())
      {
        F.print(errs());
        return true;
      }

      
      vector <string> new_variables;
      vector <AllocaInst*> ptrs;
      int index = 0;
      stringstream ss;
      for(const auto&pair : available_exp_levels)
      { 
        index++;
      }
      if(index == 1)
      {
        new_variables.push_back("temp");
      }
      else if (index > 1){
        for(int i=0; i<index; i++){
          //ss << i;
          string newstr = "temp" + to_string(i);
          new_variables.push_back(newstr);
        }
      }
      
       
      
      LLVMContext &Context = F.getContext();
      IRBuilder<> Builder(Context);
      for(auto& basic_block : F)
      {
        string bbname = basic_block.getName().str();
        if(bbname == "entry")
        {
          for(int i=0; i<new_variables.size(); i++)
          {
            Instruction *InsertionPoint = &basic_block.front();
            Type *ty = Type::getInt32Ty(Context);
            AllocaInst* newinst = new AllocaInst(ty,0,new_variables[i],InsertionPoint);
            //errs() << new_variables[i]<<"\n";
            ptrs.push_back(newinst);
            //errs() << ptrs[i]->getName().str()<<"\n";
          }
        }
      }
      map <string, int> min_levels;
      for(auto&pair : available_exp_levels)
      {
        int min = pair.second[0];
        for(int i=0; i< pair.second.size(); i++)
        {
          if (min >= pair.second[i])
          {
            min = pair.second[i];
          }
        }
        min_levels[pair.first] = min;
      }

      map <string, vector<string>> exp_block;
      /* errs() <<"available exps\n";
      for(auto& pair : available_exp_levels){
        errs() << pair.first <<"\n";
        for(int i=0;i<pair.second.size();i++)
        {
          errs() << pair.second[i] << " ";
        }
        errs() <<"\n";
        } */

      for(auto &pair : OutsBB)
      {
        string bbname = pair.first;
        for(auto&str : pair.second)
        {
          bool found = false;
          for (auto& pair : available_exp_levels) {
            if (pair.first == str) {
              found = true;
              break;
            }
          }
          if(found)
          {
          exp_block[str].push_back(bbname);
          }
        }
      }
      /* for(auto& pair : exp_block){
        errs() << pair.first <<"\n";
        for(int i=0;i<pair.second.size();i++)
        {
          errs() << pair.second[i] << " ";
        }
        errs() <<"\n";
    } */

      int varindex = -1;
       
      std::vector<Instruction*> instructionsToDelete;
      for(auto&pair : exp_block)
      {
        //errs() << "hello\n";
        varindex++;
        

        string expression = pair.first;
        int m = min_levels[expression];
        for(int i=0; i<pair.second.size();i++)
        {
          string block_name = pair.second[i];
          for(auto&basic_block : F)
          {
            string bbname = basic_block.getName().str();
            if(bbname != block_name)
              continue;
            int level = block_levels[bbname];
            bool found = false;
            for(Instruction&instruct : basic_block)
            {
              if(found)
                {
                  found = false;
                  if(level == min_levels[expression])
                  {
                    
                    Instruction *temp = &instruct;
                    Value *value = instruct.getOperand(0);
                    Value *value_e = instruct.getOperand(1);
                    
                    const Twine vartwine;
                    
                    Type *ty = Type::getInt32Ty(Context);
                    Instruction *storeInst = new StoreInst(value, ptrs[varindex], &instruct);
                    Instruction *loadi = new LoadInst(ty, ptrs[varindex],vartwine,&instruct);                   
                    Instruction *anotherstore = new StoreInst(loadi, value_e, &instruct);                  
                    instructionsToDelete.push_back(&instruct);
                             
                  }
                  else
                  {
                    
                    const Twine vartwine;
                    Value *value_e = instruct.getOperand(1);
                    Type *ty = Type::getInt32Ty(Context);
                    Instruction *loadi = new LoadInst(ty, ptrs[varindex],vartwine ,&instruct);
                    Instruction *anotherstore = new StoreInst(loadi, value_e, &instruct);
                    instructionsToDelete.push_back(&instruct);
                    

                  }
                }
              if(isa<BinaryOperator> (instruct))
              {
                string exp_vec = getExpressionFromInstruct(&instruct)[2];
                if(exp_vec.compare(expression) == 0)
                {
                  found = true;
                  if(level != min_levels[expression])
                  {
                    instructionsToDelete.push_back(&instruct);
                  }

                }
              }
              
            }
          }
        }
      }
      //errs() << "helloanother\n";
      for (Instruction* instruct : instructionsToDelete) {
        instruct->eraseFromParent();
      }

      F.print(errs());




      return true;
    }
    
    /*1. First we fetch the expression along with it's variables
       2. Add the expression in generated expressions
       3. Variables are put in a set for checking
       4. If we encounter a definition for one of these variables,
          we remove the expression from generated expressions */
    set<string> getGeneratedExpressions(BasicBlock *bb)
    {
      //Iterating over the instructions in the basic block
      set<string> genExpressions;
      set<string> defCheck;
      unordered_map<string, string> checkMap;
      string exp;
      for (Instruction &instruct: *bb)
      {
        vector<string> expressionVec;
        if (isa<BinaryOperator> (instruct))
        {
          expressionVec = getExpressionFromInstruct(&instruct);
          genExpressions.insert(expressionVec[2]);
          exp = expressionVec[2];
          defCheck.insert(expressionVec[0]);
          defCheck.insert(expressionVec[1]);
          checkMap[expressionVec[0]] = expressionVec[2];
          checkMap[expressionVec[1]] = expressionVec[2];
        }

        //Checking if a definition belongs to a variable from expression from block
        if (isa<StoreInst> (instruct))
        {
          string
          var = getVarFromInstruct(&instruct);
          if (existsKey(defCheck,
              var))
          {
            genExpressions.erase(genExpressions.find(checkMap[var]));
          }
        }
      }

      return genExpressions;
    }

    //Method returns the killed expressions of a particular basic block.
    set<string> getKilledExpressions(BasicBlock *bb, set<vector < string>> allExpressionsVec)
    {
      set<string> killedExpressions;
      for (Instruction &instruct: *bb)
      {
        if (isa<StoreInst> (instruct))
        {
          string
          var = getVarFromInstruct(&instruct);
          for (auto vecAllExp: allExpressionsVec)
          {
            if (var == vecAllExp[0] ||
              var == vecAllExp[1])
            {
              //add to kill
              killedExpressions.insert(vecAllExp[2]);
            }
          }
        }

        if (isa<BinaryOperator> (instruct))
        {
          vector<string> expressionVec = getExpressionFromInstruct(&instruct);
          if (existsKey(killedExpressions, expressionVec[2]))
          {
            killedExpressions.erase(killedExpressions.find(expressionVec[2]));
          }
        }
      }

      return killedExpressions;
    }

    //Method to extract expression from a binary instruction
    vector<string> getExpressionFromInstruct(Instruction *instruct)
    {
      vector<string> expressionVec;
      if (isa<BinaryOperator> (instruct))
      {
        BinaryOperator *binaryOp = dyn_cast<BinaryOperator> (instruct);
        string var1 = returnNameFromVal(binaryOp->getOperand(0));
        string var2 = returnNameFromVal(binaryOp->getOperand(1));
        if (isa<LoadInst> (binaryOp->getOperand(0)))
        {
          LoadInst *loadInst1 = dyn_cast<LoadInst> (binaryOp->getOperand(0));
          Value *val1 = loadInst1->getPointerOperand();
          var1 = val1->getName().str();
        }

        if (isa<LoadInst> (binaryOp->getOperand(1)))
        {
          LoadInst *loadInst2 = dyn_cast<LoadInst> (binaryOp->getOperand(1));
          Value *val2 = loadInst2->getPointerOperand();
          var2 = val2->getName().str();
        }

        expressionVec.push_back(var1);
        expressionVec.push_back(var2);
        string operatorName = binaryOp->getOpcodeName();
        string op = getOpFromOpName(operatorName);
        string expression = var1 + op + var2;
        expressionVec.push_back(expression);
      }

      return expressionVec;
    }

    /*Method to get a particular value (set < string>) in vec[2] from set<vector < string>> vec
    Parameter - set<vector < string>> vec
    Returns set<string>*/
    set<string> getSetFromVec(set<vector < string>> vec)
    {
      set<string> returnSet;
      for (auto vecElem: vec)
      {
        returnSet.insert(vecElem[2]);
      }

      return returnSet;
    }

    /*Method to get name from value eg. get operand name from value
    Parameter - Value v
    Returns string*/

    string returnNameFromVal(Value *V)
    {
      string block_address;
      raw_string_ostream string_stream(block_address);
      V->printAsOperand(string_stream, false);
      return string_stream.str();
    }

    /*Method to get operator from operator Name
    Parameter - String operatorName
    Returns string*/
    string getOpFromOpName(string operatorName)
    {
      string op;
      if (operatorName == "add")
      {
        op = "+";
      }
      else if (operatorName == "sub")
      {
        op = "-";
      }
      else if (operatorName == "mul")
      {
        op = "*";
      }
      else if (operatorName == "sdiv")
      {
        op = "/";
      }

      return op;
    }

    /*Method to get variable name from an instruction
    Parameter - Instruction
    Returns string*/
    string getVarFromInstruct(Instruction *instruct)
    {
      string result;
      if (isa<LoadInst> (*instruct))
      {
        LoadInst *loadInst = dyn_cast<LoadInst> (instruct);
        Value *useVal = loadInst->getPointerOperand();
        result = useVal->getName().str();
      }

      if (isa<StoreInst> (*instruct))
      {
        StoreInst *storeInst = dyn_cast<StoreInst> (instruct);
        Value *defVal = storeInst->getPointerOperand();
        result = defVal->getName().str();
      }

      return result;
    }

    /*Method to Iteratively prints all values in a set < string>
    Parameters - set<string>*/
    

    /*Method to Check if a string value is present in a set < string>
    Parameters - set < string>, string
    Returns bool*/
    bool existsKey(set<string> set, string key)
    {
      if (set.find(key) != set.end())
      {
        return true;
      }
      else
      {
        return false;
      }
    }
  };
  // end of struct AvailExpression
} // end of anonymous namespace

char CSElimination::ID = 0;
static RegisterPass<CSElimination> X("CSElimination", "CSElimination Pass",
  false /*Only looks at CFG */,   true /*Analysis Pass */);


