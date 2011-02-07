{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances #-}
module Test (
  
  bindingtest,
  vmtest,
  
  main
  
  ) where

import LLVMBinding hiding (TDouble)
import VM

import qualified LLVM.FFI.ExecutionEngine as Engine
import qualified LLVM.FFI.Core as LLVM
import qualified LLVM.Core as LLVMCore

import System.CPUTime

import Foreign.Ptr

import System.IO.Unsafe(unsafePerformIO)
import System.Environment

import Control.Monad

-- the LLVM Function should be of type :: void ()
runtest :: (LLVMModule -> IO LLVMFunction) -> IO ()
runtest f = do {
            -- we initialize LLVM
            ; _ <- LLVMCore.initializeNativeTarget
            ; mod <- moduleCreateWithName "LLVMTestModule"

            -- build the engine
            ; engine <- getModuleEngine mod

            -- create meme functions prototype
            ; _malloc <- addFunction2 mod "malloc" $ fctType [int32Type] (ptrType int8Type)
            ; _free <- addFunction2 mod "free" $ fctType [ptrType int8Type] voidType
            ; _memcpy <- addFunction2 mod "memcpy" $ fctType [ptrType int8Type, ptrType int8Type, int32Type] (ptrType int8Type)

            -- the test per say
            ; fct <- f mod

            -- verify the function
            ; _ <- verifyFunction fct

            -- optimize the module
            --; optimizeModule mod

            -- we compile  the function .. 
            ; (time1, _) <- timedEval $ Engine.getPointerToGlobal engine $ valOf fct
            ; putStrLn $ "compile time := " ++ show time1                                    

            -- we run the function
            ; (time1, _) <- timedEval $ runFunction engine fct []
            ; putStrLn $ "eval time := " ++ show time1                                    

            -- we dump the module
            --; _ <- LLVM.dumpModule mod

            -- show memory usage
            ; showMemUsage

            -- we clean
            -- this function is only in 0.9 ..
            --; _ <- Engine.disposeExecutionEngine engine

            -- so we can't clean the module ...
            --; _ <- LLVM.disposeModule mod
            ; return ()
}

-- simple test

bindingtest :: IO ()
bindingtest = do {
              ; let f = \ mod -> do {
                                 ; fct <- addFunction2 mod "main" $ fctType [] voidType
                                 ; builder <- createEntryBuilder fct
                                              
                                 -- GCed
                                              
                                 ; when (gcedtest testconfig) $ do {
                                                                  
                                                                ; jumpToNewBlock builder "test gced"
                                                                ; gcedp <- createGCed builder $ structType [int32Type]
                                                                ; _ <- getGCedData builder gcedp
                                                                ; incRef builder gcedp
                                                                ; decRef builder gcedp
                                                                ; decRef builder gcedp
                                                                         
                                                                }
                                        
                                 -- DynArray
                                                                   
                                 ; when (dynarraytest testconfig) $ do {
                                                                      
                                                                    ; jumpToNewBlock builder "test dynarray"
                                                                    ; arrayp <- createDynArray builder (structType [int8Type]) (integer2LLVMInteger 200 32)
                                                                    ; eltp <- lookupDynArray builder (integer2LLVMInteger 1 32) arrayp
                                                                    ; incRef builder arrayp
                                                                    ; decRef builder arrayp
                                                                    ; decRef builder arrayp

                                                                    }
                                        
                                 -- Sum

                                 ; when (sumtest testconfig) $ do {
                                                                 
                                                               ; jumpToNewBlock builder "test sum"
                                                               ; sump <- createSum builder (sumType [int32Type, structType [int8Type, int32Type]]) 0 (integer2LLVMInteger 0 32)
                                                               ; _ <- destructSum builder sump (replicate 2 $ \ builder val -> return (integer2LLVMInteger 0 32))
                                                               ; incRef builder sump
                                                               ; decRef builder sump
                                                               ; decRef builder sump

                                                               }
                                        
                                 -- Stack

                                 ; when (stacktest testconfig) $ do {
                                                                   
                                                                   
                                                                 ; jumpToNewBlock builder "test stack"
                                                                 ; stackp <- createStack builder int32Type (integer2LLVMInteger 10 32)
                                                                 ; size <- stackSize builder stackp
                                                                           
                                                                           
                                                                 ; let n = 13
                                                                 -- the native code generation completely fails on stackPush ...
                                                                 -- the datapp computed in stackPush' computed from stackPush ...
                                                                 -- don't know why the behavior is different ... 
                                                                 ; _ <- mapM (\ _ -> stackPush' builder stackp (integer2LLVMInteger 90 32)) [0..n]
                                                                 ; _ <- mapM (\ _ -> stackPop' builder stackp) [0..n]
                                                                        
                                                                 ; incRef builder stackp
                                                                 ; decRef builder stackp
                                                                 ; decRef builder stackp
                                                                          
                                                                 ; return ()
                                                                          
                                                                 }
                                        
                                 -- Recursive types
                                 ; when (rectypetest testconfig) $ do {   
                                                                     
                                                                   ; jumpToNewBlock builder "test rec type"
                                                                   ; let ty = defType "list" $ structType [ptrType $ varType "list", int8Type]
                                                                   ; ty' <- toLLVMType ty
                                                                            
                                                                   -- still an issue here ... recursive type makes fromLLVMType to never terminates ...
                                                                   --; (nty :: LLVMType) <- fromLLVMType ty'
                                                                   --; putStrLn $ show nty
                                                                            
                                                                   ; typ <- buildAlloca builder ty
                                                                   ; nullval <- constNull ty
                                                                   ; buildStore builder nullval typ
                                                                                
                                                                   ; let mutual_rec_def = [ ("tya", ptrType $ varType "tyb"),
                                                                                                                                ("tyb", structType [varType "tyb", varType "tya"])
                                                                                          ]
                                                                   ; let tys = map snd $ recDef mutual_rec_def
                                                                               
                                                                   ; stackp <- createStack builder (tys!!0) (integer2LLVMInteger 10 32)
                                                                   ; decRef builder stackp
                                                                            
                                                                   }

                                 -- closure

                                 -- simple closure without argument first
                                 -- Double -> Double -> Double = (+)

                                 -- first the function
                                  
                                 --; buildDebugMsg builder "creating dadd ..."
                                 ; mod <- getParentModule builder
                                 ; dadd <- addFunction2 mod "Dadd" $ fctType [ptrType $ structType [boolType], ptrType $ structType [doubleType, doubleType]] doubleType
                                 ; builder2 <- createEntryBuilder dadd
                                 ; env <- getParam dadd 0
                                 ; args <- getParam dadd 1
                                 ; d1p <- buildStructGEP builder2 args 0
                                 ; d2p <- buildStructGEP builder2 args 1
                                 ; d1 <- buildLoad builder2 d1p
                                 ; d2 <- buildLoad builder2 d2p
                                 ; res <- buildFAdd builder2 d1 d2
                                 ; buildRet builder2 res

                                 ; _ <- verifyFunction dadd

                                 -- createClosure :: LLVMBuilder -> [LLVMValue] {- env values -} -> [LLVMType] {- argsty -} -> LLVMType {- retty -} -> LLVMValue {- the implementation function -} -> IO LLVMValue
                                 --; buildDebugMsg builder "creating closure ..."
                                 ; cl <- createClosure builder [bool2LLVMBool True] [doubleType, doubleType] doubleType dadd


                                 ; applyClosure builder cl [double2LLVMDouble 2.0]
                                 ; applyClosure builder cl [double2LLVMDouble 1.0]

                                 ; res <- computeClosure builder cl
                                 ; buildPrintf builder "result = %g\n" [res]

                                 --; buildDebugMsg builder "deref closure ..."
                                 ; decRef builder cl

                                 -- runtime
                                           
                                 ; when (runtimetest testconfig) $ do {
                                                                     
                                                                   --; buildException builder "exception test" voidType
                                                                   --; buildDebugMsg builder "this is a message ..."

                                                                   ; showMemUsage

                                                                   ; buildPrintf builder "myprintf: %d\n" [(integer2LLVMInteger 0 32)]

                                                                   }
       
                                 -- block pointer manipulation
                                 -- definitely does not works ... SEGFAULT !!!

                                 ; _ <- buildRetVoid builder


                                 ; writeModuleToFile mod "./bindingtest.bc"
                                 --; mod' <- readModuleFromFile "./mymod.bc"
                                 --; LLVM.dumpModule mod'

                                 ; return fct
                                 }
              ; runtest f
              }
    
-- test

---------------------- Test

objectFibonacci :: Int -> ([ObjectBlock], String)
objectFibonacci n = ( [ [ (Just "fibonacci", RECURSION "6" "fibonacci" [("a", TDouble),
                                                                ("b", TDouble),
                                                                ("count", TInt)
                                                               ] (TDouble) ([], [])),
                          (Nothing, PUSH $ VDouble 1.0),
                          (Nothing, PUSH $ VDouble 0.0),
                          (Nothing, PUSH $ VInt n),
                          (Nothing, APPLY 3),
                          (Nothing, RETURN) ],

                        -- recursive entry = 6
                        [ (Just "6", ACCESSVOL 2),
                          (Nothing, PUSH $ VInt 0),
                          (Nothing, TOTPRIMITIVE PIEq),
                          (Nothing, JMPC "13"),
                          (Nothing, ACCESSVOL 0),
                          -- exitcond: 12
                          (Just "12", RETURN) ],

                        -- falsebranch: 13
                        [ (Just "13", ACCESSVOL 2),
                          (Nothing, PUSH $ VInt 1),
                          (Nothing, TOTPRIMITIVE PISub),
                          (Nothing, ACCESSVOL 0),

                          (Nothing, ACCESSVOL 0),
                          (Nothing, ACCESSVOL 1),
                          (Nothing, TOTPRIMITIVE PDAdd),

                          (Nothing, POPENV 3),
                          (Nothing, SWAP ["count", "b", "a"] 3),
                          (Nothing, JMP "6") ]
                      ],
                      "fibonacci")

testFibonacci :: Int -> Double
testFibonacci n =
    let (VAL (VDouble res)) = testVM $ objectFibonacci n in
    res


test1ObjectCode :: ([ObjectBlock], String)
test1ObjectCode = ([
                      [(Just "test1", PUSH $ VDouble 0.0),
                       (Nothing, RETURN)
                      ],

                      [(Just "test2", PUSH $ VDouble 0.0),
                       (Nothing, PUSH $ VBool False),
                       (Nothing, JMPC "test2_exit2"),
                       (Just "test2_exit1", RETURN),
                       (Just "test2_exit2", RETURN)
                      ],

                      [(Just "test3", PUSH $ VDouble 0.0),
                       (Nothing, PUSH $ VBool False),
                       (Nothing, SWAP [] 1),
                       (Nothing, RETURN)
                      ],

                      [(Just "test4", PUSH $ VDouble 0.0),
                       (Nothing, SWAP [] 1),
                       (Nothing, PRIMITIVE PDAdd),
                       (Nothing, ACCESSVOL 0),
                       (Nothing, APPLY 1),
                       (Nothing, ACCESSVOL 0),
                       (Nothing, APPLY 1),
                       (Nothing, PUSH $ VBool False),
                       (Nothing, POPENV 1),
                       (Nothing, JMPC "test4_exit2"),
                       (Just "test4_exit1", RETURN),
                       (Just "test4_exit2", RETURN)
                      ],

                      [ (Just "test5", RECURSION "test5_exit" "myrec" [("a", TDouble), ("b", TDouble)] TDouble ([], [])),
                        (Nothing, PUSH $ VDouble 0.0),
                        (Nothing, APPLY 1),
                        (Just "test5_exit", RETURN)

                      ],
                      [ (Just "test6", CONSTRUCTOR 0 "pair"),
                        (Nothing, PUSH $ VDouble 1.2),
                        (Nothing, PUSH $ VInt 1),
                        (Nothing, APPLY 2),
                        (Nothing, DESTRUCTOR ["test6_destruct"]),
                        (Just "test6_destruct", ACCESSVOL 0),
                        (Just "test6_exit", RETURN)
                      ]
                   ]
                   , "test6"
                   )

vmtest :: ([ObjectBlock], String) -> IO ()
vmtest vm = do {
            -- LLVM initialization + top module creation
            ; _ <- LLVMCore.initializeNativeTarget
            ; mod <- moduleCreateWithName "LLVMTestModule"
                     
            -- register the types
            ; regRecDef mod vmTypes

            -- create memory functions prototype
            ; _malloc <- addFunction2 mod "malloc" $ fctType [int32Type] (ptrType int8Type)
            ; _free <- addFunction2 mod "free" $ fctType [ptrType int8Type] voidType
            ; _memcpy <- addFunction2 mod "memcpy" $ fctType [ptrType int8Type, ptrType int8Type, int32Type] (ptrType int8Type)


            -- link VM code and generate interpreter
            ; let (ocode, entrylabel) = vm
            ; let (code, entry) = linkObjectBlock ocode entrylabel
            --; putStrLn $ codeBlock2String code
            ; fct <- buildTopLevel mod code entry
            -- verify the function
            ; _ <- verifyFunction fct

            -- build main function for stand-alone native compilation

            ; main <- addFunction2 mod "main" $ fctType [] voidType
                      
            ; builder <- createEntryBuilder main

            ; res <- buildCall builder fct []
                     
            ; buildPrintf builder "vmExec res := %p\n" [res]
            ; printVMData builder res

            ; buildRetVoid builder

            ; _ <- verifyFunction main

            -- optimize the module
            --; optimizeModule mod

            -- save the module for stand-alone compilation
            ; writeModuleToFile mod $ "./" ++ snd vm ++ ".bc"

            -- build the engine
            ; engine <- getModuleEngine mod

            -- we compile  the function .. 
            ; (time1, _) <- timedEval $ Engine.getPointerToGlobal engine $ valOf fct
            ; putStrLn $ "compil time := " ++ show time1                                    

            -- we run the function .. 
            ; (time1, res) <- timedEval $ runFunction engine fct []
            ; putStrLn $ "eval time := " ++ show time1
            ; showMemUsage
            ; freeGCMem

            -- we dump the module
            --; _ <- LLVM.dumpModule mod

            ; (unknownp :: Ptr ()) <- Engine.genericValueToPointer res

            ; putStrLn $ "result := " ++ show unknownp

            -- we clean
            -- this function is only in 0.9 ..
            --; _ <- Engine.disposeExecutionEngine engine


            -- so we can't clean the module ...
            --; _ <- LLVM.disposeModule mod
            ; return ()


            }

timedEval :: IO a -> IO (Double, a)
timedEval v = do {
              ; cpu1 <- getCPUTime
              ; res <- v
              ; cpu2 <- getCPUTime
              ; let time = fromIntegral (cpu2 - cpu1) * 1e-12 :: Double
              ; return (time, res)
              }

data Testconfig = Testconfig { 
  testbinding :: Bool,
  gcedtest :: Bool,
  dynarraytest :: Bool,
  sumtest :: Bool,
  stacktest :: Bool,
  rectypetest :: Bool,
  runtimetest:: Bool,
  
  testvm :: Bool
  }
              
testconfig :: Testconfig
testconfig = Testconfig { 
  testbinding = True,
  gcedtest = True,
  dynarraytest = True,
  sumtest = True,  
  stacktest = True,  
  rectypetest = True,
  runtimetest= True,
  
  testvm = True
  }             
             

main :: IO ()
main = do {
   
  ; args <- getArgs
  ; let n = if null args then 100 else read $ args!!0
                                       
  ; when (testbinding testconfig) bindingtest
            
  ; when (testvm testconfig) $ do {
    
    ; putStrLn ""
    ; (time, _) <- timedEval $ putStrLn $ "vmExec test1ObjectCode := " ++ showVMData (testVM test1ObjectCode)
    ; putStrLn $ "time := " ++ show time
      
    ; putStrLn ""
    ; putStrLn $ "llvm test1ObjectCode"
    ; vmtest test1ObjectCode
    
    ; putStrLn ""
    ; (time, _) <- timedEval $ putStrLn $ "vmExec (fibonacci " ++ show n ++ ") := " ++ show (testFibonacci n)
    ; putStrLn $ "time := " ++ show time
      
    ; let saved = (fst $ objectFibonacci n)
    ; saveObjectBlocks saved "./test.vmo"
    ; loaded <- loadObjectBlocks "./test.vmo"
    ; when (loaded /= saved) $ error $ "catastrophic: loading/unloading inconsistent"
 
      
    ; putStrLn ""
    ; putStrLn $ "llvm (fibonacci " ++ show n ++ ")"
    ; vmtest (objectFibonacci n)
      
    }  
  
  ; putStrLn ""
 
  }

