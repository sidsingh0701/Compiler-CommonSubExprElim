/*
 * File: CSE_C.c
 *
 * Description:
 *   This is where you implement the C version of project 4 support.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* LLVM Header Files */
#include "llvm-c/Core.h"
#include "dominance.h"
#include "transform.h"

/* Header file global to this project */
#include "cfg.h"
#include "CSE.h"


int CSE_Basic = 0;
int CSE_Dead  = 0;
int CSE_Simplify = 0;
int CSE_RLoad = 0;
int CSE_Store2Load = 0;
int CSE_RStore = 0;


static
int commonSubexpression(LLVMValueRef I, LLVMValueRef J) {

  // return 1 if I and J are common subexpressions
  int flag = 0;
  int flag2 = 0;
  // check these things:
  //   - they have the same opcode
  //   - they have the same type
  //   - they have the same number of operands
  //   - all operands are the same (pointer equivalence) LLVMValueRef
  // if any are false, return 0
  if(LLVMGetInstructionOpcode(I) == LLVMGetInstructionOpcode(J)){
	flag++;
	if(LLVMTypeOf(I) == LLVMTypeOf(J)){
		flag++;
		int count1 = LLVMGetNumOperands(I);
		int count2 = LLVMGetNumOperands(J);
		int count3 = 0;
		if(count1 == count2){
			flag++;
			int i;
			for(i=0;i<count1;i++)
			{
				if(LLVMGetOperand(I,i) == LLVMGetOperand(J,i))	
				 count3++;
			}
			if(count3 == count1){
				flag++;
			}
		}
			
	}
   }
   if(LLVMIsAICmpInst(I) && LLVMIsAICmpInst(J)){
	if(LLVMGetICmpPredicate(I) == LLVMGetICmpPredicate(J))
		flag2++;
   }
   if((flag == 4 && flag2 == 0) || (flag == 4 && flag2 == 1)){ 	return 1;} // CHECK FOR EXCLUSIVELY ICMP PREDICATE WITH CSE BASIC CONDS OR CSE BASIC ONLY CONDS
  // if(flag == 4)	return 1;
   else 		return 0;
  
}


static
int canHandle(LLVMValueRef I) 
{
  return ! 
    (LLVMIsALoadInst(I) ||
      LLVMIsAStoreInst(I) ||
      LLVMIsATerminatorInst(I) ||
      LLVMIsACallInst(I) ||
      LLVMIsAPHINode(I) ||
      LLVMIsAAllocaInst(I) || 
     LLVMIsAFCmpInst(I) ||
     LLVMIsAExtractValueInst(I) ||
     LLVMIsAVAArgInst(I) );
}

static int ISDEAD(LLVMValueRef I){
	if (LLVMGetFirstUse(I)!=NULL)
   	 return 0;

  LLVMOpcode opcode = LLVMGetInstructionOpcode(I); 
  switch(opcode) {
  // All of these instructions are branches or have special meaning
  case LLVMRet:
  case LLVMBr:
  case LLVMSwitch:
  case LLVMIndirectBr:
  case LLVMInvoke: 	
  case LLVMUnreachable:
  case LLVMFence:
  case LLVMStore:
  case LLVMCall:
  case LLVMAtomicCmpXchg:
  case LLVMAtomicRMW:
  case LLVMResume:	
  case LLVMLandingPad:
  case LLVMExtractValue: 
    return 0;
  // We can remove loads, but only if they are non-volatile
  case LLVMLoad: if(LLVMGetVolatile(I)) return 0;
  default:
    break;
  }
  return 1;
}


// Perform CSE on I for BB and all dominator-tree children
static
void processInst(LLVMBasicBlockRef BB, LLVMValueRef I) 
{
  // do nothing if trivially dead
  int count = ISDEAD(I);
  if(count == 1) return;
  if(!canHandle(I)) return;
  LLVMValueRef inst_iter;
  LLVMValueRef op1;
  inst_iter = LLVMGetFirstInstruction(BB); 
  // CSE w.r.t. to I on BB
  if(LLVMGetInstructionParent(I) == BB){
  	inst_iter = LLVMGetNextInstruction(I);
  }
  
  while(inst_iter !=  NULL) 
  {
		int temp1 = commonSubexpression(I,inst_iter);
	        if(temp1){
			op1 = inst_iter;
			inst_iter = LLVMGetNextInstruction(inst_iter);
			LLVMReplaceAllUsesWith(op1,I); CSE_Basic++;
			LLVMInstructionEraseFromParent(op1);
			continue;
		}
		inst_iter = LLVMGetNextInstruction(inst_iter);
				
		
  }
  

  // for each dom-tree child of BB:
  //    processInst(child)
  LLVMBasicBlockRef child = LLVMFirstDomChild(BB);
   
  while (child) {
    processInst(child,I);
    child = LLVMNextDomChild(BB,child);  // get next child of BB
 }

}



static
void FunctionCSE(LLVMValueRef Function) 
{
  LLVMBasicBlockRef BB;
  LLVMValueRef I;
  int flag = 0;


  // for each bb:
  //   for each isntruction
  //       processInst
  //
  //   process memory instructions
  LLVMBasicBlockRef bb_iter;LLVMValueRef inst_iter;
  for (bb_iter = LLVMGetFirstBasicBlock(Function);bb_iter != NULL; bb_iter = LLVMGetNextBasicBlock(bb_iter))
  {
	inst_iter = LLVMGetFirstInstruction(bb_iter);
	flag = 0;	
	while(inst_iter != NULL) 
        {
		flag = 0;

		if(ISDEAD(inst_iter) == 1) {	//DEAD CODE ELIMINATION
			LLVMValueRef op1 = inst_iter;
			inst_iter = LLVMGetNextInstruction(inst_iter);			
			CSE_Dead++;
			LLVMInstructionEraseFromParent(op1);
			continue;
		}

		LLVMValueRef opt1; // SIMPLIFY
		opt1 = InstructionSimplify(inst_iter);
		if(opt1){
			LLVMReplaceAllUsesWith(inst_iter,opt1); CSE_Simplify++;
		}
		if(LLVMIsALoadInst(inst_iter)){//REDUNDANT LOAD ELIMINATION
			LLVMValueRef iter2 = LLVMGetNextInstruction(inst_iter);	
			while(iter2 != NULL){
				if(LLVMIsAStoreInst(iter2) || LLVMIsACallInst(iter2)){
					break;
				}
				if(LLVMIsALoadInst(iter2)) {
				  if(!LLVMGetVolatile(iter2)){
					if( (LLVMTypeOf(inst_iter) == LLVMTypeOf(iter2))){
						if(LLVMGetOperand(inst_iter,0) == LLVMGetOperand(iter2,0)){
							LLVMValueRef op1 = iter2;
							iter2 = LLVMGetNextInstruction(iter2);	
							LLVMReplaceAllUsesWith(op1,inst_iter);		
							CSE_RLoad++;
							//printf("%d == %d ^^ \n",LLVMGetNumOperands(iter2));
							LLVMInstructionEraseFromParent(op1);
							continue;
						}
				   	}
				 }	
				}	
				iter2 = LLVMGetNextInstruction(iter2);
			}
		
		}

		if(LLVMIsAStoreInst(inst_iter)){//REDUNDANT STORE ELIMINATION
			LLVMValueRef iter2 = LLVMGetNextInstruction(inst_iter);
			while(iter2!=NULL){
							//	printf("Bugg2\n");
				if (LLVMIsACallInst(iter2)){
					break;
				}
				else if(LLVMIsALoadInst(iter2)){
				
									//printf("Bugg4\n");
					if(!LLVMGetVolatile(iter2)){
					
									//printf("Bugg3\n");
						//if(LLVMGetNumOperands(iter2)<2)	printf("Bugg in load\n");
						//if(LLVMGetNumOperands(inst_iter)<3)	printf("Bugg in store\n");
						if((LLVMGetOperand(iter2,0) == LLVMGetOperand(inst_iter,1))){
								
									//printf("Bugg5\n");
							if(LLVMTypeOf(iter2) == LLVMTypeOf(LLVMGetOperand(inst_iter,0))){
									LLVMValueRef op1 = iter2;
									iter2 = LLVMGetNextInstruction(iter2);	
									LLVMReplaceAllUsesWith(op1,LLVMGetOperand(inst_iter,0));		
									CSE_Store2Load++;
									//printf("Bugg1\n");
									//printf("%d == %d ^^ \n",LLVMGetNumOperands(iter2));
									LLVMInstructionEraseFromParent(op1);
									continue;	
							}
						}
					}
				}
				else if(LLVMIsAStoreInst(iter2)){
					if(LLVMGetOperand(inst_iter,1) == LLVMGetOperand(iter2,1) && LLVMTypeOf(LLVMGetOperand(inst_iter,1))==LLVMTypeOf(LLVMGetOperand(iter2,1))){

						if(!LLVMGetVolatile(inst_iter)){
									//LLVMDumpValue(inst_iter);			printf("\n"); LLVMDumpValue(iter2);
							if(LLVMTypeOf(LLVMGetOperand(inst_iter,0)) == LLVMTypeOf(LLVMGetOperand(iter2,0))){
								LLVMValueRef op1 = inst_iter;
								inst_iter = LLVMGetNextInstruction(inst_iter);		
								CSE_RStore++;
								//printf("%d == %d ^^ \n",LLVMGetNumOperands(iter2));
								LLVMInstructionEraseFromParent(op1);
								flag = 1;
								break;		
							}
						}					
					}
				}
				if(LLVMIsAStoreInst(iter2) || LLVMIsALoadInst(iter2))	break; // IGNORE STORE OR LOAD AND BREAK
			        iter2 = LLVMGetNextInstruction(iter2);
			}
		}
		processInst(bb_iter,inst_iter); //CSE_BASIC 
		if(ISDEAD(inst_iter) == 1) {	//DEAD CODE ELIMINATION
			LLVMValueRef op1 = inst_iter;
			inst_iter = LLVMGetNextInstruction(inst_iter);			
			CSE_Dead++;
			LLVMInstructionEraseFromParent(op1);
			continue;
		}
	   	if(flag == 1) continue;
	        else inst_iter = LLVMGetNextInstruction(inst_iter);
			
	   }
	}
  }
		

void LLVMCommonSubexpressionElimination(LLVMModuleRef Module)
{
  // Loop over all functions
  LLVMValueRef Function;
  for (Function=LLVMGetFirstFunction(Module);Function!=NULL;
       Function=LLVMGetNextFunction(Function))
    {
      FunctionCSE(Function);

    }
  printf("CSE_Basic CSE_Dead CSE_Simplify CSE_RLoad CSE_Store2Load CSE_RStore\n");
  printf("%d %d %d %d %d %d\n",CSE_Basic,CSE_Dead,CSE_Simplify,CSE_RLoad,CSE_Store2Load,CSE_RStore);
  // print out summary of results
}

