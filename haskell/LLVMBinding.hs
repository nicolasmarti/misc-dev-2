{-# LANGUAGE TypeSynonymInstances, PatternGuards, ScopedTypeVariables, ForeignFunctionInterface #-}


-- TODO
-- 1) implement TClosure
-- 2) implement a non-blocking fromLLVMType


module LLVMBinding (

    -- types and values
    IntegerType(..), FloatingType(..), PrimitiveType(..), AggregateType(..), 
    DerivedType(..), ManagedType(..), RecType(..), 
    LLVMType(..), LLVMValue(..), LLVMModule, LLVMFunction, LLVMBuilder, LLVMBlock,
    LLVMTypeable(..), LLVMValueable(..), LLVMComputable(..),

    -- helpers
    valOf, typeOf, freeVar,

    ptrType, int32Type, int64Type, int8Type, int16Type, int1Type, boolType,
    voidType, labelType, labelPtrType, structType, packedStructType, arrayType, fctType,
    dynDArrayType, dynArrayType, gcedDType, gcedType,
    sumDType, sumType, closureDType, closureType, stackDType,
    stackType, extractManagedType, typeCast, doubleType, floatType,
    varType, defType,
    rewrite_type, rollUp, recDef, regRecDef, unFold,

    -- basic LLVM opcode building

    isConstant, 
    
    addTypeName, constString, constArray,
    addFunction, addFunction2, createEntryBuilder, createBlock, createBuilder, cachedApplication,
    moveBuilder, getParam, getFunction, getFunction2,  getNamedGlobal, getParentModule, getParentBlock,
    moduleCreateWithName, verifyFunction,
    buildCall, buildBitCast, buildPtrToInt, buildIntToPtr, buildIntCast,
    buildGEP, buildStructGEP, buildAlloc, buildAlloc2, buildAlloca, buildFree, buildMemcpy, buildMemcpy2,
    buildExtractElem, buildExtractValue,
    buildLoad, buildStore,
    buildAdd, buildSub, buildMul, buildUDiv, buildSDiv, buildNeg, buildSRem, buildURem,
    buildFAdd, buildFSub, buildFMul, buildFDiv, buildFNeg, buildFRem,
    buildAnd, buildOr, buildNot,
    buildRetVoid, buildRet, buildSelect, buildPhi, addIncoming,
    buildSwitch, buildSwitch2, IntTest(..), buildICmp, FloatTest(..), buildFCmp, buildCondBr, buildBr, buildIndirectBr, buildUnreachable, 
    valueFromLabel, valueFromLabel2, buildIsNull, addGlobal, setInitializer, constNull, getUndef,
    sizeOf,

    buildArrayMalloc,

    jumpToNewBlock,

    cachedFunction, 

    getVarArgs, endVarArgs, buildGetVarArg,

    -- execution functions

    getModuleEngine, getModuleInterp, runFunction, optimizeModule, optimizeFunction, registerRunTime,

    -- helper functions

    integer2LLVMInteger, double2LLVMDouble, float2LLVMFloat, bool2LLVMBool,

    -- higher level codegen

    buildForLoop, buildCounterLoop,
    initData,

    -- memory managed type
    incRef, decRef, incRef', decRef', destroyManagedType, getRefCount, 
    mutateRefFirstLevel,
    createDynArray, lookupDynArray, mutateDynArray, dynArraySize, copyExtDynArray,
    createGCed, getGCedData,
    createSum, createSum2, destructSum, destructSum2, destructSum3, extractFromSum,
    createStack, stackSize, stackCapacity, stackLookup, stackMutate, stackPop, stackPop', stackPush, stackPush', stackCopy,
    createFinalizer, finalizerGetData,
    createClosure, destroyClosure, applyClosure, computeClosure,

    -- saving loading modules

    writeModuleToFile, readModuleFromFile,

    -- error function in haskell ....

    buildException, buildException2,
    llvmexception, imported_llvmexception,

    -- debug message

    buildDebugMsg,
    llvmdebugmsg, imported_llvmdebugmsg,

    -- implementation of printf

    buildPrintf, 

    -- memory allocation profiling facility

    buildRegisterAlloc, llvmRegisterAlloc, imported_llvmRegisterAlloc,
    buildRegisterFree, llvmRegisterFree, imported_llvmRegisterFree,
    showMemUsage, freeGCMem, 

    -- outSide function
    isTrue,
    
    ) where


import qualified LLVM.FFI.Core as LLVM
import qualified LLVM.FFI.Analysis as Analysis
import qualified LLVM.FFI.ExecutionEngine as Engine
import qualified LLVM.FFI.Target as Target()
import qualified LLVM.Core as LLVMCore
import qualified LLVM.FFI.Transforms.Scalar as Optim
import qualified LLVM.FFI.Transforms.IPO as Optim
import qualified LLVM.FFI.BitWriter as BitWriter
import qualified LLVM.FFI.BitReader as BitReader

import qualified Data.HashTable as HashTable

import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr
import Foreign.Marshal.Array
import Foreign.Marshal.Alloc
import Foreign.Storable hiding (sizeOf)

import Control.Monad.Trans
import Control.Monad

import Data.List(intercalate)
import Data.Maybe(isNothing, isJust, fromJust)

import qualified Data.Set as Set

import Data.IORef

import Debug.Trace

import System.IO.Unsafe(unsafePerformIO)


-- this flag control the memory profiling

memProfiling :: Bool
memProfiling = False

debugGC :: Bool
debugGC = False

-- few redefinitions for sake of readability
type LLVMModule = LLVM.ModuleRef
type LLVMBuilder = LLVM.BuilderRef
type LLVMBlock = LLVM.BasicBlockRef

type ExecutionEngineRef = Ptr Engine.ExecutionEngine

-- the types of llvm

data IntegerType = IntegerType Integer -- the size in bit
                 deriving (Eq, Ord)

instance Show IntegerType where
    show (IntegerType i) = "i" ++ show i

data FloatingType = TFloat
                  | TDouble
                  deriving (Eq, Ord)

instance Show FloatingType where
    show TFloat = "float"
    show TDouble = "double"

data PrimitiveType = TLabel
                   | TLabelPtr
                   | TInteger IntegerType
                   | TFloating FloatingType
                   | TVoid
                   deriving (Eq, Ord)

instance Show PrimitiveType where
    show TLabel = "label"
    show TLabelPtr = "label*"
    show (TInteger i) = show i
    show (TFloating f) = show f
    show TVoid = "void"

data AggregateType = TArray Integer LLVMType
                   | TStructure [LLVMType]
                   | TPackedStructure [LLVMType]
                   | TVector Integer (Either IntegerType FloatingType)
                   deriving (Eq, Ord)

instance Show AggregateType where
    show (TArray i ty) = "[" ++ show i ++ " x " ++ show ty ++ "]"
    show (TStructure tys) = "{ " ++ intercalate ", " (map show tys) ++ " }"
    show (TPackedStructure tys) = "< { " ++ intercalate ", " (map show tys) ++ " } >"
    show (TVector i (Left ty)) = "<" ++ show i ++ " x " ++ show ty ++ ">"
    show (TVector i (Right ty)) = "<" ++ show i ++ " x " ++ show ty ++ ">"

data DerivedType = TAggregate AggregateType
                 | TFunction [LLVMType] Bool LLVMType
                 | TPointer LLVMType
                 deriving (Eq, Ord)

instance Show DerivedType where
    show (TAggregate ty) = show ty
    show (TFunction tys vararg ty) = show ty ++ " (" ++ intercalate ", " (map show tys) ++ if vararg then "...)" else "" ++ ")"
    show (TPointer ty) = show ty ++ "*"

-- these types are explicitely garbage collected
data ManagedType = TDynArray LLVMType
               | TGCed LLVMType
               | TSum [LLVMType]
               | TStack LLVMType
               | TClosure [LLVMType]
               | TFinalizer LLVMType
               deriving (Eq, Ord)

instance Show ManagedType where
    show (TDynArray ty) = "[? x " ++ show ty ++ "]"
    show (TGCed ty) = "[[" ++ show ty ++ "]]"
    show (TSum tys) = "(" ++ intercalate " | " (map show tys) ++ ")"
    show (TStack ty) = "stack(" ++ show ty ++ ")"
    show (TClosure tys) = intercalate " -> " (map show $ tys)
    show (TFinalizer ty) = "finalizer(" ++ show ty ++ ")"

-- definition with alias (for recursive types)
data RecType = TDef String LLVMType
             | TVar String
             deriving (Eq, Ord)

instance Show RecType where
    show (TDef s ty) = s -- "(" ++ s ++ " := " ++ show ty ++ ")"
    show (TVar s) = s

-- all the LLVM types
data LLVMType = TPrimitive PrimitiveType
              | TDerived DerivedType
              | TManaged ManagedType
              | TRecType RecType
              deriving (Eq, Ord)

instance Show LLVMType where
    show (TPrimitive ty) = show ty
    show (TDerived ty) = show ty
    show (TManaged ty) = show ty
    show (TRecType ty) = show ty

-- some typeclass
class (Show a) => LLVMTypeable a where
    fromLLVMType :: LLVM.TypeRef -> IO a


    toLLVMType2 :: HashTable.HashTable String LLVM.TypeRef -> a -> IO LLVM.TypeRef

    toLLVMType :: a -> IO LLVM.TypeRef
    toLLVMType x = do {
                   ; hash <- HashTable.new (==) HashTable.hashString
                   ; toLLVMType2 hash x
                   }

    ptrOf :: a -> IO LLVM.TypeRef
    ptrOf x = do { ty <- toLLVMType x
                 ; return $ LLVM.pointerType ty $ fromIntegral 0
                 }



instance LLVMTypeable LLVM.TypeRef where
    toLLVMType2 h = return
    fromLLVMType = return

-- equivalence ... needed for dynamic type test
infix  4 ===

(===) :: LLVMType -> LLVMType -> Bool
(===) ty1 ty2 | ty1 == ty2 = True
(===) ty1@(TRecType (TDef _ _)) ty2 = (===) (rollUp ty1) ty2
(===) ty1 ty2@(TRecType (TDef _ _)) = (===) ty1  (rollUp ty2)
(===) _ _ = False

-- an LLVM Value is a couple of LLVM.ValueRef and a type
-- such that we have dynamic typing on building instruction
-- and avoid the incomprehensible runtime error of LLVM

--
data LLVMValue = LLVMValue LLVM.ValueRef LLVMType
               deriving (Eq, Ord)

class (LLVMTypeable a) => LLVMValueable a where
    toLLVMValue :: a -> IO LLVM.ValueRef


instance LLVMTypeable LLVMValue where
    toLLVMType2 h (LLVMValue _ ty) = toLLVMType ty

    fromLLVMType ty = do { ty' <- fromLLVMType ty
                         ; return $ LLVMValue (LLVM.constNull ty) ty'
                         }

instance LLVMValueable LLVMValue where
  toLLVMValue (LLVMValue val _) = return val

valOf :: LLVMValue -> LLVM.ValueRef
valOf (LLVMValue val _) = val

typeOf :: LLVMValue -> LLVMType
typeOf (LLVMValue _ ty) = ty

instance Show LLVMValue where
  show (LLVMValue val ty) = show val ++ " :: " ++ show ty

-- LLVMFunction are Values

type LLVMFunction = LLVMValue

--

-- some basic constructor
ptrType :: LLVMType -> LLVMType
ptrType ty = TDerived $ TPointer ty

int32Type :: LLVMType
int32Type = TPrimitive $ TInteger $ IntegerType 32

int64Type :: LLVMType
int64Type = TPrimitive $ TInteger $ IntegerType 64

int8Type :: LLVMType
int8Type = TPrimitive $ TInteger $ IntegerType 8

boolType :: LLVMType
boolType = TPrimitive $ TInteger $ IntegerType 1

int1Type :: LLVMType
int1Type = TPrimitive $ TInteger $ IntegerType 1

int16Type :: LLVMType
int16Type = TPrimitive $ TInteger $ IntegerType 16

voidType :: LLVMType
voidType = TPrimitive $ TVoid

labelType :: LLVMType
labelType = TPrimitive $ TLabel

labelPtrType :: LLVMType
labelPtrType = TPrimitive $ TLabelPtr

floatType :: LLVMType
floatType = TPrimitive $ TFloating $ TFloat

doubleType :: LLVMType
doubleType = TPrimitive $ TFloating $ TDouble

structType :: [LLVMType] -> LLVMType
structType tys = TDerived $ TAggregate $ TStructure tys

packedStructType :: [LLVMType] -> LLVMType
packedStructType tys = TDerived $ TAggregate $ TPackedStructure tys

arrayType :: Integer -> LLVMType -> LLVMType
arrayType x ty = TDerived $ TAggregate $ TArray x ty

fctType :: [LLVMType] -> LLVMType -> LLVMType
fctType args ret = TDerived $ TFunction args False ret

fctVarargType :: [LLVMType] -> LLVMType -> LLVMType
fctVarargType args ret = TDerived $ TFunction args True ret

dynDArrayType :: LLVMType -> LLVMType
dynDArrayType ty = structType [int32Type, int32Type, arrayType 0 ty]

dynArrayType :: LLVMType -> LLVMType
dynArrayType ty = TManaged $ TDynArray ty

gcedDType :: LLVMType -> LLVMType
gcedDType ty = structType [int32Type, ty]

gcedType :: LLVMType -> LLVMType
gcedType ty = TManaged $ TGCed ty

sumDType :: [LLVMType] -> LLVMType
sumDType tys = structType [int32Type, int32Type, arrayType 0 (structType tys) {- dummy type-}]

sumType :: [LLVMType] -> LLVMType
sumType tys = TManaged $ TSum tys

closureDRealType :: [LLVMType] -> [LLVMType] -> LLVMType -> LLVMType
closureDRealType envty argsty retty = structType [
                                       int32Type, {- ref counter -} 
                                       ptrType $ fctType [ptrType $ int8Type] voidType, {- the destroy function -} 
                                       ptrType $ fctVarargType [ptrType $ int8Type, int8Type] $ voidType, {- the application function -}
                                       ptrType $ fctType [ptrType $ int8Type] retty, {- the final computation function -}
                                       gcedType (structType envty), {- environment variable -}
                                       int32Type, {- trigger -}
                                       structType argsty, {- arguments -}
                                       ptrType $ fctType [ptrType $ structType envty, ptrType $ structType argsty] retty
                                      ]

-- this is obviously wrong, yet will suffice before real implmentation
closureDType :: [LLVMType] -> LLVMType
closureDType tys = structType [ int32Type,
                                ptrType $ fctType [ptrType $ int8Type] voidType,
                                ptrType $ fctVarargType [ptrType $ int8Type, int8Type] $ voidType,
                                ptrType $ fctType [ptrType $ int8Type] $ last tys
                              ]

closureType :: [LLVMType]-> LLVMType
closureType tys = TManaged $ TClosure tys

stackDType :: LLVMType -> LLVMType
stackDType ty = structType [int32Type, int32Type, int32Type, ptrType $ arrayType 0 ty]

stackType :: LLVMType -> LLVMType
stackType ty = TManaged $ TStack ty

varType :: String -> LLVMType
varType s = TRecType $ TVar s

defType :: String -> LLVMType -> LLVMType
defType s ty = TRecType $ TDef s ty

finalizerType :: LLVMType -> LLVMType
finalizerType ty = TManaged $ TFinalizer ty

finalizerDType :: LLVMType -> LLVMType
finalizerDType ty = structType [int32Type, ty, ptrType $ fctType [ty] voidType]

extractManagedType :: LLVMType -> ManagedType
extractManagedType (TManaged ty) = ty
extractManagedType ty@(TRecType (TDef _ _)) = extractManagedType $ rollUp ty
extractManagedType _ = error "not a managed type"

-- all these types implements LLVMTypeable
instance LLVMTypeable IntegerType where
  toLLVMType2 h (IntegerType i) = return $ LLVM.integerType (fromInteger i)
  fromLLVMType _ = error $ "Catastrophic: should never been called"


instance LLVMTypeable FloatingType where
  toLLVMType2 h TFloat = return LLVM.floatType
  toLLVMType2 h TDouble = return LLVM.doubleType
  fromLLVMType _ = error $ "Catastrophic: should never been called"

instance LLVMTypeable PrimitiveType where
  toLLVMType2 h TLabel = return $ LLVM.labelType
  toLLVMType2 h TLabelPtr = return $ LLVM.pointerType (LLVM.integerType (fromIntegral 8)) (fromInteger 0)
  toLLVMType2 h (TInteger ty) = toLLVMType ty
  toLLVMType2 h (TFloating ty) = toLLVMType ty
  toLLVMType2 h TVoid = return LLVM.voidType
  fromLLVMType _ = error $ "Catastrophic: should never been called"

instance LLVMTypeable AggregateType where
  toLLVMType2 h (TArray sz ty) = do { ty' <- toLLVMType2 h ty
                                 ; return $ LLVM.arrayType ty' $ fromInteger sz
                                 }
  toLLVMType2 h (TStructure tys) = do { tys' <- mapM (toLLVMType2 h) tys
                                      ; res <- liftIO $ withArrayLen tys' $ \ len ptr -> return $ LLVM.structType ptr (fromIntegral len) (fromInteger 0)
                                      ; return res
                                      }
  toLLVMType2 h (TPackedStructure tys) = do { tys' <- mapM (toLLVMType2 h) tys
                                            ; res <- liftIO $ withArrayLen tys' $ \ len ptr -> return $ LLVM.structType ptr (fromIntegral len) (fromInteger 1)
                                            ; return res
                                            }
  toLLVMType2 h (TVector sz ty) = do { ty' <- either toLLVMType toLLVMType ty
                                     ; return $ LLVM.vectorType ty' (fromInteger sz)
                                     }
  fromLLVMType _ = error $ "Catastrophic: should never been called"

instance LLVMTypeable DerivedType where
  toLLVMType2 h (TAggregate ty) = toLLVMType2 h ty
  toLLVMType2 h (TFunction argsty vararg retty) = do {
                                                  ; argsty' <- mapM (toLLVMType2 h) argsty
                                                  ; retty' <- toLLVMType2 h retty
                                                  ; res <- liftIO $ withArrayLen argsty'
                                                           $ \ len ptr -> return $ LLVM.functionType retty' ptr (fromIntegral len) (fromInteger $ if vararg then 1 else 0)
                                                  ; return res
                                                  }
  toLLVMType2 h (TPointer ty) = do { ty' <- toLLVMType2 h ty
                                   ; return $ LLVM.pointerType ty' (fromInteger 0)
                                   }
  fromLLVMType _ = error $ "Catastrophic: should never been called"

instance LLVMTypeable ManagedType where
  toLLVMType2 h (TDynArray ty) = toLLVMType2 h $ ptrType $ dynDArrayType ty
  toLLVMType2 h (TGCed ty) = toLLVMType2 h $ ptrType $ gcedDType ty
  toLLVMType2 h (TSum tys) = toLLVMType2 h $ ptrType $ sumDType tys
  toLLVMType2 h (TStack tys) = toLLVMType2 h $ ptrType $ stackDType tys
  toLLVMType2 h (TClosure tys) = toLLVMType2 h $ ptrType $ closureDType tys
  toLLVMType2 h (TFinalizer ty) = toLLVMType2 h $ ptrType $ finalizerDType ty

  fromLLVMType _ = error $ "Catastrophic: should never been called"

instance LLVMTypeable RecType where
    toLLVMType2 h (TDef s ty) = do {
                                -- opaqueTypeInContext :: ContextRef -> IO TypeRef
                                -- createTypeHandle :: TypeRef -> IO TypeHandleRef
                                -- refineType :: TypeRef -> TypeRef -> IO ()
                                -- resolveTypeHandle :: TypeHandleRef -> IO TypeRef
                                -- disposeTypeHandle :: TypeHandleRef -> IO ()
                                -- getGlobalContext :: IO ContextRef
                                ; ctxt <- LLVM.getGlobalContext
                                ; newopaque <- LLVM.opaqueTypeInContext ctxt
                                ; typeHandle <-LLVM.createTypeHandle newopaque
                                ; oldval <- HashTable.lookup h s
                                ; HashTable.insert h s newopaque
                                ; ty' <- toLLVMType2 h ty
                                ; HashTable.delete h s
                                ; when (isJust oldval) $ HashTable.insert h s $ fromJust oldval
                                ; mty <- LLVM.refineType newopaque ty'
                                ; mnewtype <- LLVM.resolveTypeHandle typeHandle
                                ; LLVM.disposeTypeHandle typeHandle
                                ; return mnewtype
                                }
    toLLVMType2 h (TVar s) = do { ty <- HashTable.lookup h s
                                ; case ty of
                                    Just ty -> return ty
                                    Nothing -> error $ "catastrophic: no registration from alias " ++ s
                                }

    fromLLVMType _ = error $ "Catastrophic: should never been called"


instance LLVMTypeable LLVMType where
  toLLVMType2 h (TPrimitive ty) = toLLVMType2 h ty
  toLLVMType2 h (TDerived ty) = toLLVMType2 h ty
  toLLVMType2 h (TManaged ty) = toLLVMType2 h ty
  toLLVMType2 h (TRecType ty) = toLLVMType2 h ty

  toLLVMType ty = do {
                 ; when (not $ Set.null $ freeVar ty) $ error $ "Catastrophic, type given to toLLVMType has free variables !!! " ++ show ty
                 ; hash <- HashTable.new (==) HashTable.hashString
                 ; toLLVMType2 hash ty
                 }


  fromLLVMType ty = do {
    ; kind <- LLVM.getTypeKind ty
    ; (case kind of
          LLVM.VoidTypeKind -> return $ TPrimitive TVoid
          LLVM.FloatTypeKind -> return $ TPrimitive $ TFloating $ TFloat
          LLVM.DoubleTypeKind -> return $ TPrimitive $ TFloating $ TDouble
          LLVM.LabelTypeKind -> return $ TPrimitive TLabel
          LLVM.IntegerTypeKind -> do { sz <- LLVM.getIntTypeWidth ty
                                     ; return $ TPrimitive $ TInteger $ IntegerType $ fromIntegral sz
                                     }
          LLVM.FunctionTypeKind -> do { retty <- LLVM.getReturnType ty
                                      ; retty' <- fromLLVMType retty
                                      ; nbargs <- LLVM.countParamTypes ty
                                      -- allocaArray :: Storable a => Int -> (Ptr a -> IO b) -> IO b
                                      ; argsty <- allocaArray (fromIntegral nbargs) $
                                                  \ ptr -> do {
                                                    -- getParamTypes :: TypeRef -> Ptr TypeRef -> IO ()
                                                    ; _ <- LLVM.getParamTypes ty ptr
                                                    -- peekArray :: Storable a => Int -> Ptr a -> IO [a]
                                                    ; argsty <- peekArray (fromIntegral nbargs) ptr
                                                    ; mapM fromLLVMType argsty
                                                    }
                                      ; isvararg <- LLVM.isFunctionVarArg ty
                                      ; return $ TDerived $ TFunction argsty (if (fromIntegral isvararg == 0) then False else True) retty'
                                      }
          LLVM.StructTypeKind -> do {
            -- countStructElementTypes :: TypeRef -> CUInt
            -- getStructElementTypes :: TypeRef -> Ptr TypeRef -> IO ()
            -- isPackedStruct :: TypeRef -> CInt
            ; let ispacked = LLVM.isPackedStruct ty
            ; let nbelt = LLVM.countStructElementTypes ty
            ; eltsty <- allocaArray (fromIntegral nbelt) $
                        \ ptr -> do {
                          ; _ <- LLVM.getStructElementTypes ty ptr
                          ; eltsty <- peekArray (fromIntegral nbelt) ptr
                          ; mapM fromLLVMType eltsty
                          }
            ; return $ TDerived $ TAggregate $ (if ispacked == (fromIntegral 0) then TStructure else TPackedStructure) eltsty
            }
          LLVM.ArrayTypeKind -> do {
            -- getElementType :: TypeRef -> IO TypeRef
            -- getArrayLength :: TypeRef -> IO CUInt
            ; eltty <- LLVM.getElementType ty
            ; eltty' <- fromLLVMType eltty
            ; sz <- LLVM.getArrayLength ty
            ; return $ TDerived $ TAggregate $ TArray (fromIntegral sz) eltty'
            }
          LLVM.PointerTypeKind -> do {
            ; ty <- LLVM.getElementType ty
            ; ty' <- fromLLVMType ty
            ; return $ TDerived $ TPointer ty'
            }
          LLVM.VectorTypeKind -> do {
            ; ty <- LLVM.getElementType ty
            ; ty' <- fromLLVMType ty
            -- getVectorSize :: TypeRef -> IO CUInt
            ; sz <- LLVM.getVectorSize ty
            ; return $ TDerived $ TAggregate $ TVector (fromIntegral sz) (case ty' of
                                                                             TPrimitive (TInteger ty) -> Left ty
                                                                             TPrimitive (TFloating ty) -> Right ty
                                                                             _ -> error $ "Catastrophic: vector of neither integer of floating type"
                                                                         )
            }
          _ -> error $ "unsupported LLVM Type"
      )
    }

-- function for Recursive type
rewrite_type :: LLVMType -> String -> LLVMType -> LLVMType
rewrite_type ty@(TPrimitive _) _ _ = ty

rewrite_type (TDerived (TAggregate (TArray sz ty))) s ty' = (TDerived (TAggregate (TArray sz $ rewrite_type ty s ty')))
rewrite_type (TDerived (TAggregate (TStructure tys))) s ty' = (TDerived (TAggregate (TStructure $ map (\ x -> rewrite_type x s ty') tys)))
rewrite_type (TDerived (TAggregate (TPackedStructure tys))) s ty' = (TDerived (TAggregate (TPackedStructure $ map (\ x -> rewrite_type x s ty') tys)))
rewrite_type ty@(TDerived (TAggregate (TVector _ _))) s ty' = ty

rewrite_type (TDerived (TFunction argsty vararg retty)) s ty' = (TDerived (TFunction (map (\ x -> rewrite_type x s ty') argsty) vararg $ rewrite_type retty s ty'))

rewrite_type (TDerived (TPointer ty)) s ty' = (TDerived (TPointer $ rewrite_type ty s ty'))

rewrite_type (TManaged (TGCed ty)) s ty' = (TManaged (TGCed $ rewrite_type ty s ty'))
rewrite_type (TManaged (TFinalizer ty)) s ty' = (TManaged (TFinalizer $ rewrite_type ty s ty'))
rewrite_type (TManaged (TDynArray ty)) s ty' = (TManaged (TDynArray $ rewrite_type ty s ty'))
rewrite_type (TManaged (TSum tys)) s ty' = (TManaged (TSum $ map (\ x -> rewrite_type x s ty') tys))
rewrite_type (TManaged (TStack ty)) s ty' = (TManaged (TStack $ rewrite_type ty s ty'))
rewrite_type (TManaged (TClosure tys)) s ty' = (TManaged (TClosure (map (\ x -> rewrite_type x s ty') tys)))

rewrite_type t@(TRecType (TDef s' ty)) s ty' | s == s' = t
                                             | otherwise = (TRecType (TDef s' $ rewrite_type ty s ty'))

rewrite_type t@(TRecType (TVar s')) s ty' | s == s' = ty'
                                          | otherwise = t

rollUp :: LLVMType -> LLVMType
rollUp ty@(TRecType (TDef s ty')) = let res = unFold $ rewrite_type ty' s ty in
                                    if not $ Set.null $ freeVar res then error $ "catastrophic: the rollingup have free variables !!!" ++ intercalate "\n -> \n" [show ty, show res] else rollUp res
rollUp ty | Set.null $ freeVar ty = ty
rollUp ty = error $ "catastrophic: the type have free variables !!! " ++ show (freeVar ty) ++ " \\in " ++ show ty

-- to clean a bit ...
unFold :: LLVMType -> LLVMType
unFold ty = unFold' Set.empty ty
    where
      unFold' :: Set.Set String -> LLVMType -> LLVMType
      unFold' s (TDerived (TAggregate (TArray sz ty))) = (TDerived (TAggregate (TArray sz $ unFold' s ty)))
      unFold' s (TDerived (TAggregate (TStructure tys))) = (TDerived (TAggregate (TStructure $ map (unFold' s) tys)))
      unFold' s (TDerived (TAggregate (TPackedStructure tys))) = (TDerived (TAggregate (TPackedStructure $ map (unFold' s) tys)))
      unFold' s (TDerived (TFunction argsty vararg retty)) = (TDerived (TFunction (map (unFold' s) argsty) vararg $ unFold' s retty))
      unFold' s (TDerived (TPointer ty)) = (TDerived (TPointer $ unFold' s ty))
      unFold' s (TManaged (TDynArray ty)) = (TManaged (TDynArray $ unFold' s ty))
      unFold' s (TManaged (TSum tys)) = (TManaged (TSum $ map (unFold' s) tys))
      unFold' s (TManaged (TStack ty)) = (TManaged (TStack $ unFold' s ty))
      unFold' s (TManaged (TClosure tys)) = (TManaged (TClosure (map (unFold' s) tys)))
      unFold' s (TRecType (TDef s' ty)) = if Set.member s' s then TRecType $ TVar s' else (TRecType (TDef s' $ unFold' (Set.insert s' s) ty))
      unFold' _ ty = ty


freeVar :: LLVMType -> Set.Set String
freeVar (TDerived (TAggregate (TArray sz ty))) = freeVar ty
freeVar (TDerived (TAggregate (TStructure tys))) = foldl Set.union Set.empty $ map freeVar tys
freeVar (TDerived (TAggregate (TPackedStructure tys))) = foldl Set.union Set.empty $ map freeVar tys
freeVar (TDerived (TFunction argsty vararg retty)) = Set.union (freeVar retty) $ foldl Set.union Set.empty $ map freeVar argsty
freeVar (TDerived (TPointer ty)) = freeVar ty
freeVar (TManaged (TDynArray ty)) = freeVar ty
freeVar (TManaged (TSum tys)) = foldl Set.union Set.empty $ map freeVar tys
freeVar (TManaged (TStack ty)) = freeVar ty
freeVar (TManaged (TClosure tys)) = foldl Set.union Set.empty $ map freeVar tys
freeVar (TRecType (TDef s ty)) = Set.delete s $ freeVar ty
freeVar (TRecType (TVar s)) = Set.singleton s
freeVar _ = Set.empty

-- a simple fixpoint (with error if a symbol is not present
recDef :: [(String, LLVMType)] -> [(String, LLVMType)]
recDef lst =
    let (names, defs) = unzip lst in
    let tys = map (\ (s, ty) -> TRecType $ TDef s ty) lst in
    let rewrites = zip names tys in
    let rectys = map (\ ty ->
                          until (\ ty ->
                                     let fvs = freeVar ty in
                                     if Set.null fvs then True else
                                         let lookups = map (\ hd -> (hd, lookup hd lst)) $ Set.toList fvs in
                                         let missing = filter (\ (_, hd) -> isNothing hd) lookups in
                                         if length missing > 0 then error $ "catastrophic: a symbol is not defined, " ++ show (fst $ head missing)
                                         else False

                                )
                          (\ ty -> foldl (\ acc (s, ty') -> rewrite_type acc s ty') ty rewrites)
                          ty
                     ) tys in
                 zip names $ map unFold rectys

-- register the types
regRecDef :: LLVMModule -> [(String, LLVMType)] -> IO ()
regRecDef mod types = do { _ <- mapM (\ (s, ty) -> addTypeName mod ty s) types
                         ; return ()
                         }

-- helper function
isaLLVMFct :: LLVMValue -> Bool
isaLLVMFct (LLVMValue _ (TDerived (TPointer (TDerived (TFunction _ _ _))))) = True
isaLLVMFct (LLVMValue val ty@(TRecType (TDef _ _))) = isaLLVMFct (LLVMValue val $ rollUp ty)
isaLLVMFct _ = False

llvmFctArgs :: LLVMType -> [LLVMType]
llvmFctArgs (TDerived (TPointer (TDerived (TFunction args _ _)))) = args
llvmFctArgs ty@(TRecType (TDef _ _)) = llvmFctArgs $ rollUp ty
llvmFctArgs _ = error $ "Not a function"

llvmFctRet :: LLVMType -> LLVMType
llvmFctRet (TDerived (TPointer (TDerived (TFunction _ _ ret)))) = ret
llvmFctRet ty@(TRecType (TDef _ _)) = llvmFctRet $ rollUp ty
llvmFctRet _ = error $ "Not a function"

structEltTys :: LLVMType -> [LLVMType]
structEltTys (TDerived (TPointer (TDerived (TAggregate (TStructure tys))))) = tys
structEltTys (TDerived (TPointer (TDerived (TAggregate (TPackedStructure tys))))) = tys
structEltTys ty@(TRecType (TDef _ _)) = structEltTys $ rollUp ty
structEltTys (TDerived (TPointer ty@(TRecType (TDef _ _)))) = structEltTys $ TDerived $ TPointer $ rollUp ty
structEltTys _ = error "Not a structure"

gcedEltTy :: LLVMType -> LLVMType
gcedEltTy (TManaged (TGCed ty)) = ty
gcedEltTy ty@(TRecType (TDef _ _)) = gcedEltTy $ rollUp ty
gcedEltTy _ = error "not a GCed type"

dynArrayEltTy :: LLVMType -> LLVMType
dynArrayEltTy (TManaged (TDynArray ty)) = ty
dynArrayEltTy ty@(TRecType (TDef _ _)) = dynArrayEltTy $ rollUp ty
dynArrayEltTy _ = error "not a dyarray type"

ptrDataTy :: LLVMType -> LLVMType
ptrDataTy (TDerived (TPointer ty)) = ty
ptrDataTy ty@(TRecType (TDef _ _)) = ptrDataTy $ rollUp ty
ptrDataTy _ = error " not a pointer"

areValidArgsTy :: [LLVMValue] -> LLVMValue -> Bool
areValidArgsTy args fct =
  let fctargsty = llvmFctArgs $ typeOf fct
      argsty = map typeOf args
  in
   foldl (&&) True $ zipWith (===) argsty fctargsty

isaPtr :: LLVMValue -> Bool
isaPtr (LLVMValue _ (TDerived (TPointer _))) = True
isaPtr (LLVMValue _ (TPrimitive TLabelPtr)) = True
isaPtr (LLVMValue val ty@(TRecType (TDef _ _))) = isaPtr $ (LLVMValue val $ rollUp ty)
isaPtr _ = False

isaInt :: LLVMValue -> Bool
isaInt (LLVMValue _ (TPrimitive (TInteger _))) = True
isaInt (LLVMValue val ty@(TRecType (TDef _ _))) = isaInt $ (LLVMValue val $ rollUp ty)
isaInt _ = False

isaFloating :: LLVMValue -> Bool
isaFloating (LLVMValue _ (TPrimitive (TFloating _))) = True
isaFloating (LLVMValue val ty@(TRecType (TDef _ _))) = isaFloating $ (LLVMValue val $ rollUp ty)
isaFloating _ = False

isaVector :: LLVMValue -> Bool
isaVector (LLVMValue _ (TDerived (TAggregate (TVector _ _)))) = True
isaVector (LLVMValue val ty@(TRecType (TDef _ _))) = isaVector $ (LLVMValue val $ rollUp ty)
isaVector _ = False

isaIntVector :: LLVMValue -> Bool
isaIntVector (LLVMValue _ (TDerived (TAggregate (TVector _ (Left _))))) = True
isaIntVector (LLVMValue val ty@(TRecType (TDef _ _))) = isaIntVector $ (LLVMValue val $ rollUp ty)
isaIntVector _ = False

isaFloatingVector :: LLVMValue -> Bool
isaFloatingVector (LLVMValue _ (TDerived (TAggregate (TVector _ (Right _))))) = True
isaFloatingVector (LLVMValue val ty@(TRecType (TDef _ _))) = isaFloatingVector $ (LLVMValue val $ rollUp ty)
isaFloatingVector _ = False

isaBool :: LLVMValue -> Bool
isaBool (LLVMValue _ (TPrimitive (TInteger (IntegerType 1)))) = True
isaBool (LLVMValue val ty@(TRecType (TDef _ _))) = isaBool $ (LLVMValue val $ rollUp ty)
isaBool _ = False

gepType :: LLVMValue -> [LLVMValue] -> IO LLVMType
gepType (LLVMValue _ (TDerived (TPointer ty))) (ind:tl) = getType' ty tl
gepType (LLVMValue val ty@(TRecType (TDef _ _))) indices = gepType (LLVMValue val $ rollUp ty) indices
gepType val indices = error $ "gepType: wrong value/indices, " ++ show (val, indices)
    
getType' :: LLVMType -> [LLVMValue] -> IO LLVMType
getType' ty [] = return $ ptrType ty
getType' (TDerived (TAggregate (TStructure tys))) (ind:tl) = do { val <- LLVM.constIntGetZExtValue $ valOf ind
                                                                ; let val' = fromIntegral val
                                                                ; getType' (tys!!val') tl
                                                                }
getType' (TDerived (TAggregate (TPackedStructure tys))) (ind:tl) = do { val <- LLVM.constIntGetZExtValue $ valOf ind
                                                                      ; let val' = fromIntegral val
                                                                      ; getType' (tys!!val') tl
                                                                      }
getType' (TDerived (TAggregate (TArray _ ty))) (ind:tl) = getType' ty tl
getType' ty indices = error $ "getType: " ++ show ty ++ " ? [" ++ intercalate ", " (map show indices) ++ "]"

-- not sure for this one ...
isaValidIndicePtr :: [LLVMValue] -> LLVMValue -> Bool
isaValidIndicePtr indices ptr = True

isaStructPtr :: LLVMValue -> Bool
isaStructPtr (LLVMValue _ (TDerived (TPointer (TDerived (TAggregate (TStructure _)))))) = True
isaStructPtr (LLVMValue _ (TDerived (TPointer (TDerived (TAggregate (TPackedStructure _)))))) = True
isaStructPtr (LLVMValue val ty@(TRecType (TDef _ _))) = isaStructPtr $ (LLVMValue val $ rollUp ty)
isaStructPtr (LLVMValue val (TDerived (TPointer ty@(TRecType (TDef _ _))))) = isaStructPtr $ (LLVMValue val $ TDerived $ TPointer $ rollUp ty)
isaStructPtr _ = False

isaValidStructIndex :: LLVMValue -> Int -> Bool
isaValidStructIndex (LLVMValue _ (TDerived (TPointer (TDerived (TAggregate (TStructure tys)))))) i = i < length tys
isaValidStructIndex (LLVMValue _ (TDerived (TPointer (TDerived (TAggregate (TPackedStructure tys)))))) i = i < length tys
isaValidStructIndex (LLVMValue val ty@(TRecType (TDef _ _))) i = isaValidStructIndex (LLVMValue val $ rollUp ty) i
isaValidStructIndex (LLVMValue val (TDerived (TPointer ty@(TRecType (TDef _ _))))) i = isaValidStructIndex (LLVMValue val $ TDerived $ TPointer $ rollUp ty) i
isaValidStructIndex _ _ = False

isaValidValuePtr :: LLVMValue -> LLVMValue -> Bool
isaValidValuePtr (LLVMValue _ ty) (LLVMValue _ (TDerived (TPointer ty'))) = ty === ty'
isaValidValuePtr _ _ = False

isaLabel :: LLVMValue -> Bool
isaLabel (LLVMValue _ (TPrimitive TLabel)) = True
isaLabel (LLVMValue val ty@(TRecType (TDef _ _))) = isaLabel (LLVMValue val $ rollUp ty)
isaLabel _ = False

isaLabelPtr :: LLVMValue -> Bool
isaLabelPtr (LLVMValue _ (TPrimitive TLabelPtr)) = True
isaLabelPtr (LLVMValue val ty@(TRecType (TDef _ _))) = isaLabelPtr (LLVMValue val $ rollUp ty)
isaLabelPtr _ = False

typeCast :: LLVMValue -> LLVMType -> LLVMValue
typeCast (LLVMValue val _) ty = LLVMValue val ty


-- might be usefull some day ...

class LLVMComputable a where
  toLLVMComputation :: a -> LLVMBuilder -> IO LLVMValue


writeModuleToFile :: LLVMModule -> String -> IO ()
writeModuleToFile mod name = do { cname <- newCString name
                                   -- writeBitcodeToFile :: ModuleRef -> CString -> IO CInt
                                 ; rc <- BitWriter.writeBitcodeToFile mod cname
                                 ; when (rc /= 0) $
                                        ioError $ userError $ "writeBitcodeToFile: return code " ++ show rc
                                 ; _ <- free cname
                                 ; return ()
                                 }

readModuleFromFile :: String -> IO LLVMModule
readModuleFromFile name = do {
                          ; cname <- newCString name
                          ; alloca $ \ bufPtr ->
                              alloca $ \ modPtr ->
                              alloca $ \ errStr -> do {
                                                   ; rrc <- LLVM.createMemoryBufferWithContentsOfFile cname bufPtr errStr
                                                   ; if rrc /= 0 then do {
                                                                      ; msg <- peek errStr >>= peekCString
                                                                      ; ioError $ userError $ "readBitcodeFromFile: read return code " ++ show rrc ++ ", " ++ msg
                                                                      }
                                                     else do {
                                                          ; buf <- peek bufPtr
                                                          ; prc <- BitReader.parseBitcode buf modPtr errStr
	                                                  ; if prc /= 0 then do {
                                                                             ; msg <- peek errStr >>= peekCString
                                                                             ; ioError $ userError $ "readBitcodeFromFile: parse return code " ++ show prc ++ ", " ++ msg
                                                                             }
                                                            else do {
                                                                 ; ptr <- peek modPtr
                                                                 ; _ <- free cname
                                                                 ; return $ ptr
                                                                 }
                                                          }

                                                   }
                          }

isConstant :: LLVMValue -> IO Bool
isConstant val = do {
    ; res <- LLVM.isConstant $ valOf val
    ; return $ res /= 0
    }
                 
isNull :: LLVMValue -> IO Bool                 
isNull val = do {
    ; res <- LLVM.isNull $ valOf val
    ; return $ res /= 0
    }


--addTypeName :: ModuleRef -> CString -> TypeRef -> IO CInt
addTypeName :: LLVMModule -> LLVMType -> String -> IO ()
addTypeName mod ty name = do { cname <- newCString name
                             ; ty' <- toLLVMType ty
                             ; _ <- LLVM.addTypeName mod cname ty'
                             ; _ <- free cname
                             ; return ()
                             }

addFunction :: LLVMModule -> String -> [LLVMType] -> LLVMType -> IO LLVMFunction
addFunction mod name argsty retty = do { cname <- newCString name
                                       ; fctty <- toLLVMType $ fctType argsty retty
                                       ; fct <- LLVM.addFunction mod cname fctty
                                       ; _ <- free cname
                                       ; return $ LLVMValue fct $ ptrType $ fctType argsty retty
                                       }

addFunction2 :: LLVMModule -> String -> LLVMType -> IO LLVMFunction
addFunction2 mod name fty = do { cname <- newCString name
                               ; fctty <- toLLVMType fty
                               ; fct <- LLVM.addFunction mod cname fctty
                               ; _ <- free cname
                               ; return $ LLVMValue fct $ ptrType fty
                               }

cachedApplication :: LLVMBuilder -> String -> LLVMType -> (LLVMBuilder -> [LLVMValue] -> IO (Maybe LLVMValue)) -> [LLVMValue] -> IO LLVMValue
cachedApplication builder fctname fctty codegen args = do {
  ; let (TDerived (TFunction argsty False retty)) = rollUp fctty
  ; mod <- getParentModule builder
  ; f <- getFunction2 mod fctname $ ptrType fctty
  ; f <- (case f of 
             Just f -> do {
               --; putTraceMsg $ "cachedApplication: already build " ++ fctname
               ; return f
               }
             Nothing -> do {
               --; putTraceMsg $ "cachedApplication: building " ++ fctname
               ; fct <- addFunction2 mod fctname fctty
               ; builder <- createEntryBuilder fct
               --; buildDebugMsg builder $ "exec start: " ++ fctname
               ; args <- mapM (\ i -> getParam fct $ fromIntegral i) $ [0..(length argsty - 1)]
               ; res <- codegen builder args
               --; buildDebugMsg builder $ "exec stop: " ++ fctname
               ; case res of
                 Nothing -> buildRetVoid builder
                 Just res -> buildRet builder res
               --; putTraceMsg $ "cachedApplication: " ++ fctname ++ " build"
               ; _ <- verifyFunction fct
               --; putTraceMsg $ "cachedApplication: " ++ fctname ++ " verified"
               ; LLVM.setFunctionCallConv (valOf fct) $ LLVM.fromCallingConvention LLVM.Fast                      
               ; optimizeFunction fct
               ; return fct
               }
         )
  ; res <- buildCall builder f args
  ; LLVM.setInstructionCallConv (valOf res) $ LLVM.fromCallingConvention LLVM.Fast
  ; return res
  }

getNamedGlobal :: LLVMModule -> String -> IO (Maybe LLVMValue)
getNamedGlobal mod name = do { cname <- newCString name
                             ; fct <- LLVM.getNamedGlobal mod cname
                             ; _ <- free cname
                             ; if fct == nullPtr then return Nothing else do {
                               ; fctty <- LLVM.typeOf fct
                               ; fctty' <- fromLLVMType fctty
                               ; return $ Just (LLVMValue fct fctty')
                               }
                             }

createEntryBuilder :: LLVMFunction -> IO LLVMBuilder
createEntryBuilder val | isaLLVMFct val = do { entryname <- newCString "entry"
                                             ; bb <- LLVM.appendBasicBlock (valOf val) entryname
                                             ; _ <- free entryname
                                             ; builder <- LLVM.createBuilder
                                             ; _ <- LLVM.positionAtEnd builder bb
                                             ; return builder
                                             }
                       | otherwise = error $ "createEntryBuilder: val not a function by of type: " ++ show val

createBuilder :: LLVMBlock -> IO LLVMBuilder
createBuilder block = do { builder <- LLVM.createBuilder
                         ; _ <- LLVM.positionAtEnd builder block
                         ; return builder
                         }

moveBuilder :: LLVMBuilder -> LLVMBlock -> IO ()
moveBuilder builder bb = do { _ <- liftIO $ LLVM.positionAtEnd builder bb
                            ; return ()
                            }

getParam :: LLVMFunction -> Integer -> IO LLVMValue
getParam fct i | isaLLVMFct fct = return $ LLVMValue (LLVM.getParam (valOf fct) (fromIntegral i)) $ (llvmFctArgs $ typeOf fct)!!(fromIntegral i)
               | otherwise = error $ "getParam: val not a function by of type: " ++ show fct

-- it should be an extern function without TManaged types or TRecType
getFunction :: LLVMModule -> String -> IO (Maybe LLVMFunction)
getFunction mod name = do { cname <- newCString name
                          ; fct <- LLVM.getNamedFunction mod cname
                          ; _ <- free cname
                          ; if fct == nullPtr then return Nothing else do {
                            ; fctty <- LLVM.typeOf fct
                            ; fctty' <- fromLLVMType fctty
                            ; return $ Just (LLVMValue fct fctty')
                            }
                          }

-- this one takes an additional arguments: a LLVMType not reconstructible from LLVM.TypeRef
getFunction2 :: LLVMModule -> String -> LLVMType -> IO (Maybe LLVMFunction)
getFunction2 mod name ty = do { cname <- newCString name
                              ; fct <- LLVM.getNamedFunction mod cname
                              ; _ <- free cname
                              ; if fct == nullPtr then return Nothing else return $ Just (LLVMValue fct ty)
                              }


createBlock :: LLVMBuilder -> String -> IO LLVMBlock
createBlock builder name = do {
  ; bb <- LLVM.getInsertBlock builder
  ; f <- LLVM.getBasicBlockParent bb
  ; blockname <- newCString name
  ; nb <- LLVM.appendBasicBlock f blockname
  ; _ <- free blockname
  ; return nb
  }

getParentModule :: LLVMBuilder -> IO LLVMModule
getParentModule builder = do {
                          ; bb <- LLVM.getInsertBlock builder
                          ; f <- LLVM.getBasicBlockParent bb
                          ; mod <- liftIO $ LLVM.getGlobalParent $ f
                          ; return mod
                          }

getParentBlock :: LLVMBuilder -> IO LLVMBlock
getParentBlock builder = do {
  ; bb <- LLVM.getInsertBlock builder
  ; return bb
  }

moduleCreateWithName :: String -> IO LLVMModule
moduleCreateWithName name = do { mname <- newCString name
                               ; mod <- LLVM.moduleCreateWithName mname
                               ; _ <- free mname
                               ; return mod
                               }

jumpToNewBlock :: LLVMBuilder -> String -> IO ()
jumpToNewBlock builder name = do {
  ; newb <- createBlock builder name
  ; buildBr builder newb
  ; moveBuilder builder newb
  }

cachedFunction :: LLVMModule -> String -> LLVMType -> (LLVMBuilder -> LLVMValue -> IO (Maybe LLVMValue)) -> IO LLVMValue
cachedFunction mod fctname fctty codegen = do {
                                           ; f <- getFunction2 mod fctname $ ptrType fctty
                                           ; case f of 
                                               Just f -> return f
                                               Nothing -> do {
                                                          ; fct <- addFunction2 mod fctname fctty
                                                          ; builder <- createEntryBuilder fct
                                                          ; res <- codegen builder fct
                                                          ; case res of 
                                                              Nothing -> buildRetVoid builder
                                                              Just val -> buildRet builder val
                                                          ; _ <- verifyFunction fct                                         
                                                          ; optimizeFunction fct
                                                          ; return fct
                                                          }
                                           }
    

getVarArgs :: LLVMBuilder -> LLVMValue -> IO (LLVMValue {- the list address (to be given to enVarArgs -} , LLVMValue {- pointer on the first elem -})
getVarArgs builder fct = do {
                         ; ap <- buildAlloca builder $ ptrType int8Type
                         ; ap2 <- buildBitCast builder ap $ ptrType int8Type

                         ; mod <- getParentModule builder
                         ; f <- getFunction mod "llvm.va_start" 
                         ; f <- case f of 
                                  Nothing -> do {
                                             ; addFunction2 mod "llvm.va_start" $ fctType [ptrType int8Type] voidType
                                             }
                                  Just f -> return f

                         ; _ <- buildCall builder f [ap2]

                         ; return (ap2, ap)

                         }

endVarArgs :: LLVMBuilder -> LLVMValue -> IO ()
endVarArgs builder valist = do {
                            ; mod <- getParentModule builder
                            ; f <- getFunction mod "llvm.va_end" 
                            ; f <- case f of 
                                     Nothing -> do {
                                                ; addFunction2 mod "llvm.va_end" $ fctType [ptrType int8Type] voidType
                                                }
                                     Just f -> return f
                                                   
                            ; _ <- buildCall builder f [valist]
                                   
                            ; return ()
                            }

--buildVAArg :: BuilderRef -> ValueRef -> TypeRef -> CString -> IO ValueRef
buildGetVarArg :: LLVMBuilder -> LLVMValue -> LLVMType -> IO LLVMValue
buildGetVarArg builder valist ty = do {
                                   ; cname <- newCString "vaarg"
                                   ; ty' <- toLLVMType ty
                                   ; res <- LLVM.buildVAArg builder (valOf valist) ty' cname
                                   ; _ <- free cname
                                   ; return $ LLVMValue res $ ty
                                   }

-- | wrapper for LLVM.verifyFunction :: ValueRef -> VerifierFailureAction -> IO CInt
verifyFunction :: LLVMFunction -> IO Integer
verifyFunction f | isaLLVMFct f = do { res <- Analysis.verifyFunction (valOf f) (fromInteger 0)
                                     ; return (toInteger res)
                                     }
                 | otherwise = error $ "verifyFunction: not a function, " ++ show f

integer2LLVMInteger :: Integer -- the integer
                    -> Integer -- size in bits
                    -> LLVMValue
integer2LLVMInteger v sz = LLVMValue (LLVM.constInt (LLVM.integerType $ fromInteger sz) (fromInteger v) 0) $ TPrimitive $ TInteger $ IntegerType sz

float2LLVMFloat :: Float -> LLVMValue
float2LLVMFloat val = LLVMValue (LLVM.constReal LLVM.floatType $ realToFrac val) floatType

double2LLVMDouble :: Double -> LLVMValue
double2LLVMDouble val = LLVMValue (LLVM.constReal LLVM.doubleType $ realToFrac val) doubleType

bool2LLVMBool :: Bool -> LLVMValue
bool2LLVMBool True = integer2LLVMInteger 1 1
bool2LLVMBool False = integer2LLVMInteger 0 1

-- instruction building
buildCall :: LLVMBuilder -> LLVMFunction -> [LLVMValue] -> IO LLVMValue
buildCall builder fct args | isaLLVMFct fct && areValidArgsTy args fct = do {
  ; cname <- newCString $ ""
  ; args' <- mapM toLLVMValue args
  ; res <- withArrayLen args' $ \ len ptr -> LLVM.buildCall builder (valOf fct) ptr (fromIntegral len) cname
  ; _ <- free cname
  ; return $ LLVMValue res $ llvmFctRet $ typeOf fct
  }
                           | not (isaLLVMFct fct) = error $ "buildCall: not a function, " ++ show fct
                           | not (areValidArgsTy args fct) = error $ "buildCall: args types does not match fct types, " ++ intercalate "\n" ["args := " ++ show args, "fct := " ++ show fct]

                           | otherwise = error "Catastrophic, should never be here"


buildBitCast :: LLVMBuilder -> LLVMValue -> LLVMType -> IO LLVMValue
buildBitCast builder val ty = do { cname <- newCString "cast"
                                 ; ty' <- toLLVMType ty
                                 ; res <- LLVM.buildBitCast builder (valOf val) ty' cname
                                 ; _ <- free cname
                                 ; return $ LLVMValue res ty
                                 }

-- | wrapper for LLVM.buildPtrToInt :: BuilderRef -> ValueRef -> TypeRef -> CString -> IO ValueRefSource
buildPtrToInt :: LLVMBuilder -> LLVMValue -> LLVMType -> IO LLVMValue
buildPtrToInt builder ptr ty@(TPrimitive (TInteger (IntegerType sz))) | isaPtr ptr = do { ty' <- toLLVMType ty
                                                                                        ; cname <- newCString "ptrtoint"
                                                                                        ; res <- LLVM.buildPtrToInt builder (valOf ptr) ty' cname
                                                                                        ; _ <- free cname
                                                                                        ; return $ LLVMValue res ty
                                                                                        }
                                                                      | otherwise = error $ "buildPtrToInt: not a pointer type, " ++ show ptr
buildPtrToInt builder ptr ty = error $ "Not an integer type, " ++ show ty

-- | wrapper for LLVM.buildIntToPtr :: BuilderRef -> ValueRef -> TypeRef -> CString -> IO ValueRef
buildIntToPtr :: LLVMBuilder -> LLVMValue -> LLVMType  -> IO LLVMValue
buildIntToPtr builder val ty@(TDerived (TPointer _)) | isaInt val = do { ty' <- toLLVMType ty
                                                                       ; cname <- newCString "inttoptr"
                                                                       ; res <- LLVM.buildIntToPtr builder (valOf val) ty' cname
                                                                       ; _ <- free cname
                                                                       ; return $ LLVMValue res ty
                                                                       }
                                                     | otherwise = error $ "buildIntToPtr: not an int, " ++ show val

buildIntToPtr builder val ty = error $ "buildIntToPtr: not a pointer type, " ++ show ty


--buildTruncOrBitCast :: BuilderRef -> ValueRef -> TypeRef -> CString -> IO ValueRef
--buildZExtOrBitCast :: BuilderRef -> ValueRef -> TypeRef -> CString -> IO ValueRef
--buildSExtOrBitCast :: BuilderRef -> ValueRef -> TypeRef -> CString -> IO ValueRef

buildIntCast :: LLVMBuilder -> LLVMValue -> LLVMType -> Bool -> IO LLVMValue
buildIntCast builder val ty@(TPrimitive (TInteger (IntegerType dst))) signed | isaInt val = do {
                                                                                            ; cname <- newCString "intCast"
                                                                                            ; let (TPrimitive (TInteger (IntegerType src))) = typeOf val
                                                                                            ; ty' <- toLLVMType ty
                                                                                            ; res <- if src > dst then 
                                                                                                         LLVM.buildTruncOrBitCast builder (valOf val) ty' cname
                                                                                                     else
                                                                                                         (if signed then LLVM.buildSExtOrBitCast else LLVM.buildZExtOrBitCast) builder (valOf val) ty' cname
                                                                                            ; _ <- free cname
                                                                                            ; return $ LLVMValue res ty
                                                                                            }
                                                                     | otherwise = error $ "buildIntCast: not an int, " ++ show val
buildIntCast builder val ty signed = error $ "buildIntCast: not a int, " ++ show ty

-- | wrapper for LLVM.buildGEP :: BuilderRef -> ValueRef -> Ptr ValueRef -> CUInt -> CString -> IO ValueRef
buildGEP :: LLVMBuilder -> LLVMValue -> [LLVMValue] -> IO LLVMValue
buildGEP builder ptr indices | (foldl (&&) True (map isaInt indices)) && isaPtr ptr && isaValidIndicePtr indices ptr = do { cname <- newCString "gep"
                                                                                                                          ; let indices' = map valOf indices
                                                                                                                          ; res <- withArrayLen indices' $ \ len aptr -> LLVM.buildGEP builder (valOf ptr) aptr (fromIntegral len) cname
                                                                                                                          ; _ <- free cname
                                                                                                                          ; ty <- gepType ptr indices
                                                                                                                          ; return $ LLVMValue res ty
                                                                                                                          }
                             | not (foldl (&&) True (map isaInt indices)) = error $ "buildGEP: all indices are not Integer, " ++ show indices

                             | not (isaValidIndicePtr indices ptr) = error $ "buildGEP: indices does not match the type, " ++ show (ptr, indices)
                             | otherwise = error $ "buildGEP: not a pointer type, " ++ show ptr

buildStructGEP :: LLVMBuilder -> LLVMValue -> Int -> IO LLVMValue
buildStructGEP builder ptr index | isaStructPtr ptr && isaValidStructIndex ptr index = do {
  ; cname <- newCString "structgep"
  ; res <- LLVM.buildStructGEP builder (valOf ptr) (fromIntegral index) cname
  ; _ <- free cname
  ; return $ LLVMValue res $ ptrType ((structEltTys $ typeOf ptr)!!index)
  }
                                 | not (isaStructPtr ptr) = error $ "buildStructGEP: not a struct pointer, " ++ show ptr
                                 | otherwise = error $ "buildStructGEP: not a valid index, " ++ show (ptr, index)

buildAlloc :: LLVMBuilder -> LLVMType -> IO LLVMValue
buildAlloc builder ty = do { sz <- sizeOf builder ty

                           --; szty <- LLVM.typeOf sz
                           --; szty' <- fromLLVMType szty

                           -- here we grab the module directly
                           ; bb <- LLVM.getInsertBlock builder
                           ; f <- LLVM.getBasicBlockParent bb
                           ; mod <- LLVM.getGlobalParent f
                           -- by convention we need "malloc" to point to malloc
                           ; Just fct <- getFunction mod "malloc"

                           --; buildPrintf builder ("memalloc(%d) :: " ++ show ty ++ "\n") [sz]

                           ; mem <- buildCall builder fct [sz]

                           ; when memProfiling $ buildRegisterAlloc builder $ typeCast mem $ TDerived $ TPointer ty

                           -- just for debug
                           --; LLVM.dumpValue $ valOf mem

                           ; res <- buildBitCast builder mem $ TDerived $ TPointer ty
                           ; return res
                           }

buildInternAlloc :: LLVMBuilder -> LLVMType -> IO LLVMValue
buildInternAlloc builder ty = do { sz <- sizeOf builder ty
                                         
                                 --; szty <- LLVM.typeOf sz
                                 --; szty' <- fromLLVMType szty
                                   
                                 -- here we grab the module directly
                                 ; bb <- LLVM.getInsertBlock builder
                                 ; f <- LLVM.getBasicBlockParent bb
                                 ; mod <- LLVM.getGlobalParent f
                                 -- by convention we need "malloc" to point to malloc
                                 ; Just fct <- getFunction mod "malloc"
                                               
                                 --; buildPrintf builder ("memalloc(%d) :: " ++ show ty ++ "\n") [sz]
                                               
                                 ; mem <- buildCall builder fct [sz]
                                          
                                 -- just for debug
                                 --; LLVM.dumpValue $ valOf mem
                                        
                                 ; res <- buildBitCast builder mem $ TDerived $ TPointer ty
                                 ; return res
                                 }


buildAlloc2 :: LLVMBuilder -> LLVMValue {- size :: int32Type -} -> LLVMType -> IO LLVMValue
buildAlloc2 builder sz ty | isaInt sz = do {
                                        -- here we grab the module directly
                                        ; bb <- LLVM.getInsertBlock builder
                                        ; f <- LLVM.getBasicBlockParent bb
                                        ; mod <- LLVM.getGlobalParent f
                                        -- by convention we need "malloc" to point to malloc
                                        ; Just fct <- getFunction mod "malloc"

                                        ; mem <- buildCall builder fct [sz]

                                        ; when memProfiling $ buildRegisterAlloc builder $ typeCast mem $ TDerived $ TPointer ty

                                        ; res <- buildBitCast builder mem $ TDerived $ TPointer ty
                                        ; return res
                                        }

                          | otherwise = error $ "buildAlloc2: not a int value, " ++ show sz

buildAlloca :: LLVMBuilder -> LLVMType -> IO LLVMValue
buildAlloca builder ty = do { cname <- newCString "alloca"
                            ; ty' <- toLLVMType ty
                            ; res <- LLVM.buildAlloca builder ty' cname
                            ; _ <- free cname
                            ; return $ LLVMValue res $ ptrType ty
                            }

buildFree :: LLVMBuilder -> LLVMValue -> IO ()
buildFree builder ptr | isaPtr ptr = do {

                                     ; when memProfiling $ buildRegisterFree builder ptr
                                     -- here we grab the module directly (WARNING: will lead to crash if several module are used !!!)
                                     ; bb <- LLVM.getInsertBlock builder
                                     ; f <- LLVM.getBasicBlockParent bb
                                     ; mod <- LLVM.getGlobalParent f
                                     -- by convention we need "free" to point to free
                                     ; Just fct <- getFunction mod "free"
                                     -- some security cast
                                     ; ptr' <- buildBitCast builder ptr ((llvmFctArgs $ typeOf fct)!!0)
                                     ; _ <- buildCall builder fct [ptr']
                                     ; return ()
                                     }
                      | otherwise = error $ "buildFree: not a pointer value, " ++ show ptr

buildInternFree :: LLVMBuilder -> LLVMValue -> IO ()
buildInternFree builder ptr | isaPtr ptr = do {
                                             
                                           -- here we grab the module directly (WARNING: will lead to crash if several module are used !!!)
                                           ; bb <- LLVM.getInsertBlock builder
                                           ; f <- LLVM.getBasicBlockParent bb
                                           ; mod <- LLVM.getGlobalParent f
                                           -- by convention we need "free" to point to free
                                           ; Just fct <- getFunction mod "free"
                                           -- some security cast
                                           ; ptr' <- buildBitCast builder ptr ((llvmFctArgs $ typeOf fct)!!0)
                                           ; _ <- buildCall builder fct [ptr']
                                           ; return ()
                                           }
                            | otherwise = error $ "buildFree: not a pointer value, " ++ show ptr
                                    

buildMemcpy :: LLVMBuilder -> LLVMValue -> LLVMValue -> LLVMType -> IO LLVMValue
buildMemcpy builder dst src ty | isaPtr dst && isaPtr src = do { sz <- sizeOf builder ty

                                                               --; szty <- LLVM.typeOf sz
                                                               --; szty' <- fromLLVMType szty

                                                               -- here we grab the module directly (WARNING: will lead to crash if several module are used !!!)
                                                               ; bb <- liftIO $ LLVM.getInsertBlock builder
                                                               ; f <- liftIO $ LLVM.getBasicBlockParent bb
                                                               ; mod <- liftIO $ LLVM.getGlobalParent f
                                                               -- by convention we need "memcpy" to point to memcpy
                                                               ; Just fct <- getFunction mod "memcpy"
                                                               -- some security cast
                                                               ; dst' <- buildBitCast builder dst ((llvmFctArgs $ typeOf fct)!!0)
                                                               ; src' <- buildBitCast builder src ((llvmFctArgs $ typeOf fct)!!0)

                                                               ; mem <- buildCall builder fct [dst', src', sz]
                                                               -- might need to check that the size matches (maybe in some debug mode)
                                                               ; return mem
                                                               }

                               | not (isaPtr dst) = error $ "buildMemcpy: destination is not a pointer, " ++ show dst
                               | otherwise = error $ "buildMemcpy: source is not a pointer, " ++ show src
-- same but precising the size
buildMemcpy2 :: LLVMBuilder -> LLVMValue -> LLVMValue -> LLVMValue -> IO LLVMValue
buildMemcpy2 builder dst src size | isaPtr dst && isaPtr src = do {
                                                               -- here we grab the module directly (WARNING: will lead to crash if several module are used !!!)
                                                               ; bb <- liftIO $ LLVM.getInsertBlock builder
                                                               ; f <- liftIO $ LLVM.getBasicBlockParent bb
                                                               ; mod <- liftIO $ LLVM.getGlobalParent f
                                                               -- by convention we need "memcpy" to point to memcpy
                                                               ; Just fct <- getFunction mod "memcpy"
                                                               -- some security cast
                                                               ; dst' <- buildBitCast builder dst ((llvmFctArgs $ typeOf fct)!!0)
                                                               ; src' <- buildBitCast builder src ((llvmFctArgs $ typeOf fct)!!0)

                                                               ; sz' <- LLVM.constIntCast (valOf size) LLVM.int32Type (fromIntegral 0)

                                                               ; mem <- buildCall builder fct [dst', src', LLVMValue sz' int32Type]
                                                               -- might need to check that the size matches (maybe in some debug mode)
                                                               ; return mem
                                                               }

                               | not (isaPtr dst) = error $ "buildMemcpy2: destination is not a pointer, " ++ show dst
                               | otherwise = error $ "buildMemcpy2: source is not a pointer, " ++ show src

--buildExtractElement :: BuilderRef -> ValueRef -> ValueRef -> CString -> IO ValueRef
buildExtractElem :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildExtractElem builder val index = do { cname <- newCString "extractelem"
                                        ; res <- LLVM.buildExtractElement builder (valOf val) (valOf index) cname
                                        ; _ <- free cname
                                        ; retty <- getType' (typeOf val) [index]
                                        ; return $ LLVMValue res retty
                                        }

buildExtractValue :: LLVMBuilder -> LLVMValue -> Int -> IO LLVMValue
buildExtractValue builder val index = do { cname <- newCString "extractvalue"
                                           ; res <- LLVM.buildExtractValue builder (valOf val) (fromIntegral index) cname
                                           ; _ <- free cname                                                
                                           ; retty <- LLVM.typeOf res
                                           ; retty' <- fromLLVMType retty
                                           ; return $ LLVMValue res retty'
                                           }

buildLoad :: LLVMBuilder -> LLVMValue -> IO LLVMValue
buildLoad builder ptr | isaPtr ptr = do { cname <- newCString "load"
                                       ; res <- LLVM.buildLoad builder (valOf ptr) cname
                                       ; _ <- free cname
                                       ; return $ LLVMValue res $ ptrDataTy $ typeOf ptr
                                       }
                      | otherwise = error $ "buildLoad: not a pointer, " ++ show ptr

buildStore :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO ()
buildStore builder val ptr | isaPtr ptr && isaValidValuePtr val ptr = do { _ <- LLVM.buildStore builder (valOf val) (valOf ptr)
                                                                         ; return ()
                                                                         }
                           | not (isaPtr ptr) = error $ "buildStore: no a pointer, " ++ show ptr
                           | otherwise = error $ "buildStore, pointer and value type does not match, \n" ++ intercalate "\nVs\n" ["ptr := " ++ show ptr, "val := " ++ show val]

buildAdd :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildAdd builder x y | typeOf x == typeOf y && (isaInt x || isaIntVector x) = do { cname <- newCString "add"
                                                                                 ; res <- LLVM.buildAdd builder (valOf x) (valOf y) cname
                                                                                 ; _ <- free cname
                                                                                 ; return $ LLVMValue res $ typeOf x
                                                                                 }
                     | not (isaInt x || isaIntVector x) = error $ "buildAdd: value is not addeable, " ++ show x
                     | otherwise = error $ "buildAdd: types mismatch, " ++ show (x, y)


buildSub :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildSub builder x y | typeOf x == typeOf y && (isaInt x || isaIntVector x) = do { cname <- newCString "sub"
                                                                                 ; res <- LLVM.buildSub builder (valOf x) (valOf y) cname
                                                                                 ; _ <- free cname
                                                                                 ; return $ LLVMValue res $ typeOf x
                                                                                 }
                     | not (isaInt x || isaIntVector x) = error $ "buildSub: value is not addeable, " ++ show x
                     | otherwise = error $ "buildSub: types mismatch, " ++ show (x, y)


buildMul :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildMul builder x y | typeOf x == typeOf y && (isaInt x || isaIntVector x) = do { cname <- newCString "mul"
                                                                                 ; res <- LLVM.buildMul builder (valOf x) (valOf y) cname
                                                                                 ; _ <- free cname
                                                                                 ; return $ LLVMValue res $ typeOf x
                                                                                 }
                     | not (isaInt x || isaIntVector x) = error $ "buildMul: value is not addeable, " ++ show x
                     | otherwise = error $ "buildMul: types mismatch, " ++ show (x, y)

buildUDiv :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildUDiv builder x y | typeOf x == typeOf y && (isaInt x || isaIntVector x) = do { cname <- newCString "udiv"
                                                                                  ; res <- LLVM.buildUDiv builder (valOf x) (valOf y) cname
                                                                                  ; _ <- free cname
                                                                                  ; return $ LLVMValue res $ typeOf x
                                                                                  }
                      | not (isaInt x || isaIntVector x) = error $ "buildUDiv: value is not addeable, " ++ show x
                      | otherwise = error $ "buildUDiv: types mismatch, " ++ show (x, y)

buildSDiv :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildSDiv builder x y | typeOf x == typeOf y && (isaInt x || isaIntVector x) = do { cname <- newCString "sdiv"
                                                                                  ; res <- LLVM.buildSDiv builder (valOf x) (valOf y) cname
                                                                                  ; _ <- free cname
                                                                                  ; return $ LLVMValue res $ typeOf x
                                                                                  }
                      | not (isaInt x || isaIntVector x) = error $ "buildSDiv: value is not addeable, " ++ show x
                      | otherwise = error $ "buildSDiv: types mismatch, " ++ show (x, y)

buildNeg :: LLVMBuilder -> LLVMValue -> IO LLVMValue
buildNeg builder x | (isaInt x || isaIntVector x) = do { cname <- newCString "neg"
                                                        ; res <- LLVM.buildNeg builder (valOf x) cname
                                                        ; _ <- free cname
                                                        ; return $ LLVMValue res $ typeOf x
                                                        }
                      | otherwise = error $ "buildNeg: types mismatch, " ++ show x

buildSRem :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildSRem builder x y | typeOf x == typeOf y && (isaInt x || isaIntVector x) = do { cname <- newCString "srem"
                                                                                 ; res <- LLVM.buildSRem builder (valOf x) (valOf y) cname
                                                                                 ; _ <- free cname
                                                                                 ; return $ LLVMValue res $ typeOf x
                                                                                 }
                     | not (isaInt x || isaIntVector x) = error $ "buildSRem: value is not addeable, " ++ show x
                     | otherwise = error $ "buildSRem: types mismatch, " ++ show (x, y)

buildURem :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildURem builder x y | typeOf x == typeOf y && (isaInt x || isaIntVector x) = do { cname <- newCString "urem"
                                                                                  ; res <- LLVM.buildURem builder (valOf x) (valOf y) cname
                                                                                  ; _ <- free cname
                                                                                  ; return $ LLVMValue res $ typeOf x
                                                                                  }
                     | not (isaInt x || isaIntVector x) = error $ "buildURem: value is not addeable, " ++ show x
                     | otherwise = error $ "buildURem: types mismatch, " ++ show (x, y)

buildFAdd :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildFAdd builder x y | typeOf x == typeOf y && (isaFloating x || isaFloatingVector x) = do { cname <- newCString "fadd"
                                                                                            ; res <- LLVM.buildFAdd builder (valOf x) (valOf y) cname
                                                                                            ; _ <- free cname
                                                                                            ; return $ LLVMValue res $ typeOf x
                                                                                            }
                     | not (isaFloating x || isaFloatingVector x) = error $ "buildFAdd: value is not addeable, " ++ show x
                     | otherwise = error $ "buildFAdd: types mismatch, " ++ show (x, y)

buildFSub :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildFSub builder x y | typeOf x == typeOf y && (isaFloatingVector x || isaFloating x) = do { cname <- newCString "fsub"
                                                                                            ; res <- LLVM.buildFSub builder (valOf x) (valOf y) cname
                                                                                            ; _ <- free cname
                                                                                            ; return $ LLVMValue res $ typeOf x
                                                                                            }
                     | not (isaFloatingVector x || isaFloating x) = error $ "buildFSub: value is not addeable, " ++ show x
                     | otherwise = error $ "buildFSub: types mismatch, " ++ show (x, y)

buildFMul :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildFMul builder x y | typeOf x == typeOf y && (isaFloating x || isaFloatingVector x) = do { cname <- newCString "fmul"
                                                                                            ; res <- LLVM.buildFMul builder (valOf x) (valOf y) cname
                                                                                            ; _ <- free cname
                                                                                            ; return $ LLVMValue res $ typeOf x
                                                                                            }
                     | not (isaFloating x || isaFloatingVector x) = error $ "buildFMul: value is not addeable, " ++ show x
                     | otherwise = error $ "buildFMul: types mismatch, " ++ show (x, y)

buildFDiv :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildFDiv builder x y | typeOf x == typeOf y && (isaFloating x || isaFloatingVector x) = do { cname <- newCString "fdiv"
                                                                                            ; res <- LLVM.buildFDiv builder (valOf x) (valOf y) cname
                                                                                            ; _ <- free cname
                                                                                            ; return $ LLVMValue res $ typeOf x
                                                                                            }
                     | not (isaFloating x || isaFloatingVector x) = error $ "buildFDiv: value is not addeable, " ++ show x
                     | otherwise = error $ "buildFDiv: types mismatch, " ++ show (x, y)

buildFNeg :: LLVMBuilder -> LLVMValue -> IO LLVMValue
buildFNeg builder x | (isaFloating x || isaFloatingVector x) = do { cname <- newCString "fneg"
                                                                  ; res <- LLVM.buildFNeg builder (valOf x) cname
                                                                  ; _ <- free cname
                                                                  ; return $ LLVMValue res $ typeOf x
                                                                  }
                    | otherwise = error $ "buildFNeg: types mismatch, " ++ show x

buildAnd :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildAnd builder b1 b2 | isaBool b1 && isaBool b2 = do { cname <- newCString "and"
                                                       ; res <- LLVM.buildAnd builder (valOf b1) (valOf b2) cname
                                                       ; _ <- free cname
                                                       ; return $ LLVMValue res $ boolType
                                                       }
                       | otherwise = error $ "buildAnd: types mismatch, " ++ show (b1, b2)

buildOr :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildOr builder b1 b2 | isaBool b1 && isaBool b2 = do { cname <- newCString "or"
                                                       ; res <- LLVM.buildOr builder (valOf b1) (valOf b2) cname
                                                       ; _ <- free cname
                                                       ; return $ LLVMValue res $ boolType
                                                       }
                       | otherwise = error $ "buildAnd: types mismatch, " ++ show (b1, b2)

buildNot :: LLVMBuilder -> LLVMValue -> IO LLVMValue
buildNot builder b1 | isaBool b1 = do { cname <- newCString "not"
                                      ; res <- LLVM.buildNot builder (valOf b1) cname
                                      ; _ <- free cname
                                      ; return $ LLVMValue res $ boolType
                                      }
                    | otherwise = error $ "buildNot: types mismatch, " ++ show b1

buildFRem :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue
buildFRem builder x y | typeOf x == typeOf y && (isaFloating x || isaFloatingVector x) = do { cname <- newCString "frem"
                                                                                            ; res <- LLVM.buildFRem builder (valOf x) (valOf y) cname
                                                                                            ; _ <- free cname
                                                                                            ; return $ LLVMValue res $ typeOf x
                                                                                            }
                      | not (isaFloating x || isaFloatingVector x) = error $ "buildFRem: value is not addeable, " ++ show x
                      | otherwise = error $ "buildFRem: types mismatch, " ++ show (x, y)

buildRetVoid :: LLVMBuilder -> IO ()
buildRetVoid builder = do { _ <- LLVM.buildRetVoid builder
                          ; return ()
                          }

buildRet :: LLVMBuilder -> LLVMValue -> IO ()
buildRet builder val = do { _ <- LLVM.buildRet builder $ valOf val
                          -- N.B.: maybe we should verify that the type is coherent with the parent function returned type
                          ; return ()
                          }

-- TODO: missing a type check for vector / bool
buildSelect :: LLVMBuilder -> LLVMValue -> LLVMValue -> LLVMValue -> IO LLVMValue
buildSelect builder cond valtrue valfalse | typeOf valtrue == typeOf valfalse = do {
                                                                                ; cname <- newCString "select"
                                                                                ; res <- LLVM.buildSelect builder (valOf cond) (valOf valtrue) (valOf valfalse) cname
                                                                                ; _ <- free cname
                                                                                ; return $ LLVMValue res $ typeOf valtrue
                                                                                }
                                          | otherwise = error $ "buildSelect: branch are not of the same type, " ++ show (valtrue, valfalse)

buildPhi :: LLVMBuilder -> LLVMType -> IO LLVMValue
buildPhi builder ty = do { cname <- newCString "phi"
                         ; ty' <- toLLVMType ty
                         ; res <- LLVM.buildPhi builder ty' cname
                         ; _ <- free cname
                         ; return $ LLVMValue res ty
                         }

addIncoming :: LLVMValue -> [(LLVMValue, LLVMBlock)] -> IO ()
addIncoming phi income = do {
  -- first build the two lists of LLVM.ValueRef
  ; let (l1, l2) = unzip income
  ; let l1' = map valOf l1
  ; let l2' = map LLVM.basicBlockAsValue l2
  -- add the cases
  ; res <- liftIO $ withArrayLen l1' (\ len1 ptr1 ->
                                       withArrayLen l2' ( \len2 ptr2 ->
                                                           LLVM.addIncoming (valOf phi) ptr1 ptr2 $ fromIntegral len1
                                                        )
                                     )
  ; return ()
  }

-- should verify that types are coherent
buildSwitch :: LLVMBuilder -> LLVMValue -> [(LLVMValue, LLVMBlock)] -> LLVMBlock -> IO ()
buildSwitch builder index cases defaultcase = do {
  ; let len = length cases
  ; switch <- LLVM.buildSwitch builder (valOf index) defaultcase $ fromIntegral len
  ; _ <- mapM (\ (hd1, hd2) -> LLVM.addCase switch (valOf hd1) hd2) cases
  ; return ()
  }

-- with error default case and automatic returning of values
buildSwitch2 :: LLVMBuilder -> LLVMValue -> [(LLVMValue, LLVMBuilder -> IO LLVMValue)] -> IO LLVMValue
buildSwitch2 builder index cases = do {
                                   ; let len = length cases

                                   ; caseblocks <- mapM (\ i -> createBlock builder $ "case_" ++ show i) [0..len - 1]

                                   ; errorblock <- createBlock builder "error_block"

                                   ; endblock <- createBlock builder "end_block"

                                   ; switch <- LLVM.buildSwitch builder (valOf index) errorblock $ fromIntegral len
                                   ; _ <- mapM (\ (hd1, hd2) -> LLVM.addCase switch (valOf hd1) hd2) $ zip (map fst cases) caseblocks

                                   ; moveBuilder builder errorblock
                                   ; buildException2 builder ("wrong tag")                                                     
                                                     
                                   ; res <- mapM (\ (i, b) -> do {
                                                              ; moveBuilder builder b
                                                              ; res <- (snd (cases!!i)) builder
                                                              ; b <- getParentBlock builder
                                                              ; buildBr builder endblock
                                                              ; return (res, b)
                                                              }) $ zip [0..len-1] caseblocks

                                   ; moveBuilder builder endblock

                                   ; fres <- buildPhi builder (typeOf $ fst $ res!!0)

                                   ; addIncoming fres res

                                   ; return fres
                                   }


data IntTest = IEQ
             | INE
             | IUGT
             | IUGE
             | IULT
             | IULE
             | ISGT
             | ISGE
             | ISLT
             | ISLE
               deriving (Enum, Show)

intTest2Cint :: IntTest -> CInt
intTest2Cint test = (fromIntegral $ fromEnum test + 32) -- enum LLVMIntPredicate has the offset 32. See llvm-c/Core.h

buildICmp :: LLVMBuilder -> IntTest -> LLVMValue -> LLVMValue -> IO LLVMValue
buildICmp builder test x y | isaInt x && typeOf x == typeOf y = do { cname <- newCString $ show test
                                                                   ; res <- LLVM.buildICmp builder (intTest2Cint test) (valOf x) (valOf y) cname
                                                                   ; _ <- free cname
                                                                   ; return $ LLVMValue res $ boolType
                                                                   }
                           | not (isaInt x) = error $ "buildICmp: not an int, " ++ show x
                           | otherwise = error $ "buildICmp: types mismatch, " ++ show (x, y)

data FloatTest = FFalse
               | FOEQ
               | FOGT
               | FOGE
               | FOLT
               | FOLE
               | FONE
               | FORD
               | FUNO
               | FUEQ
               | FUGT
               | FUGE
               | FULT
               | FULE
               | FUNE
               | FTrue
               deriving (Enum, Show)

floatTest2Cint :: FloatTest -> CInt
floatTest2Cint test = (fromIntegral $ fromEnum test) -- enum LLVMIntPredicate has the offset 32. See llvm-c/Core.h

buildFCmp :: LLVMBuilder -> FloatTest -> LLVMValue -> LLVMValue -> IO LLVMValue
buildFCmp builder test x y | isaFloating x && typeOf x == typeOf y = do { cname <- newCString $ show test
                                                                        ; res <- LLVM.buildFCmp builder (floatTest2Cint test) (valOf x) (valOf y) cname
                                                                        ; _ <- free cname
                                                                        ; return $ LLVMValue res $ boolType
                                                                        }
                           | not (isaFloating x) = error $ "buildFCmp: not an floating, " ++ show x
                           | otherwise = error $ "buildFCmp: types mismatch, " ++ show (x, y)


buildCondBr :: LLVMBuilder -> LLVMValue -> LLVMBlock -> LLVMBlock -> IO ()
buildCondBr builder b c1 c2 | isaBool b = do { _ <- LLVM.buildCondBr builder (valOf b) c1 c2
                                             ; return ()
                                             }
                            | otherwise = error $ "buildConBr: not a bool, " ++ show b

buildBr :: LLVMBuilder -> LLVMBlock -> IO ()
buildBr builder c = do { _ <- LLVM.buildBr builder c
                       ; return ()
                       }

buildIndirectBr :: LLVMBuilder -> LLVMValue -> [LLVMBlock] -> IO ()
buildIndirectBr builder label blocks | isaLabelPtr label = do {
                                                           ; indbr <- LLVM.buildIndirectBr builder (valOf label) $ fromIntegral 0
                                                           ; _ <- mapM (\ b -> LLVM.addDestination indbr b) blocks
                                                           ; return ()
                                                           }
                                     | otherwise = error $ "buildIndirectBr: not a label, " ++ show label
                                                   
buildUnreachable :: LLVMBuilder -> IO ()
buildUnreachable builder = do { 
                           ; LLVM.buildUnreachable builder
                           ; return ()
                           }

valueFromLabel :: LLVMBlock -> IO LLVMValue
valueFromLabel block = do {
                       ; f <- LLVM.getBasicBlockParent block
                       ; val <- LLVM.blockAddress f block
                       ; return $ LLVMValue val $ labelPtrType
                       }

valueFromLabel2 :: LLVMFunction -> LLVMBlock -> IO LLVMValue
valueFromLabel2 f block = do {
                        ; val <- LLVM.blockAddress (valOf f) block
                        ; return $ LLVMValue val $ labelPtrType
                        }

buildIsNull :: LLVMBuilder -> LLVMValue -> IO LLVMValue
buildIsNull builder val = do { cname <- newCString $ show "isNull"
                             ; res <- LLVM.buildIsNull builder (valOf val) cname
                             ; _ <- free cname
                             ; return $ LLVMValue res $ boolType
                             }

addGlobal :: LLVMModule -> LLVMType -> String -> IO LLVMValue
addGlobal mod ty name = do { mname <- newCString name
                           ; gcty <- toLLVMType ty
                           ; res <- LLVM.addGlobal mod gcty mname
                           ; _ <- free mname
                           ; return $ LLVMValue res $ ptrType ty
                           }

setInitializer :: LLVMValue -> LLVMValue -> IO ()
setInitializer glob val | isaValidValuePtr val glob = LLVM.setInitializer (valOf glob) (valOf val)
                        | otherwise = error $ "setInitializer: value type and pointer type mismatch, " ++ show (val, glob)


constNull :: LLVMType -> IO LLVMValue
constNull ty = do { gcty <- toLLVMType ty
                  ; return $ LLVMValue (LLVM.constNull gcty) ty
                  }

getUndef :: LLVMType -> IO LLVMValue
getUndef ty = do { gcty <- toLLVMType ty
                 ; return $ LLVMValue (LLVM.getUndef gcty) ty
                 }

-- a real dynamic sizeOf
sizeOf :: LLVMBuilder -> LLVMType -> IO LLVMValue {- :: int32Type -}
sizeOf builder ty = do {
                    ; nullp <- constNull $ ptrType ty
                    ; datasz <- buildGEP builder nullp [(integer2LLVMInteger 1 32)]
                    ; sz' <- buildPtrToInt builder datasz int64Type
                    ; sz <- buildIntCast builder sz' int32Type False
                    ; return sz
                    }

buildArrayMalloc :: LLVMBuilder -> LLVMType -> LLVMValue -> IO LLVMValue
buildArrayMalloc builder ty size | isaInt size = do {
                                                 ; cname <- newCString $ show "buildArraMalloc"
                                                 ; ty' <- toLLVMType ty
                                                 ; res <- LLVM.buildArrayMalloc builder ty' (valOf size) cname

                                                 ; when memProfiling $ buildRegisterAlloc builder $ LLVMValue res $ ptrType ty

                                                 ; _ <- free cname
                                                 ; return $ LLVMValue res $ ptrType ty
                                                 }
                                 | otherwise = error $ "buildArrayMAlloc: size not a int, " ++ show size

-- execution engine and all ...

registerRunTime :: LLVMModule -> ExecutionEngineRef -> String -> Ptr () -> IO ()
registerRunTime mod engine fctname fctptr = do {
                                            ; f <- getFunction mod fctname
                                            ; case f of
                                                Nothing -> return ()
                                                Just f -> Engine.addGlobalMapping engine (valOf f) fctptr
                                            }


getModuleEngine :: LLVMModule -> IO (ExecutionEngineRef)
getModuleEngine mod = do { modprov <- LLVM.createModuleProviderForExistingModule mod
                         ; (alloca $ \ eePtr ->
                                alloca $ \errPtr -> do {
                                                    ; engine <- do {
                                                                ; ret <- Engine.createExecutionEngine eePtr modprov errPtr
                                                                --; ret <- Engine.createInterpreter eePtr modprov errPtr
                                                                ; if ret == 1 then do err <- peek errPtr
                                                                                      errStr <- peekCString err
                                                                                      free err
                                                                                      ioError . userError $ errStr
                                                                  else
                                                                      peek eePtr
                                                                }
                                                    -- here we install by hand some runtime function ()
                                                    -- addGlobalMapping :: ExecutionEngineRef -> ValueRef -> Ptr () -> IO ()
                                                    -- function only add if requested ...

                                                    ; let runtime_fct = [ ("llvmexception", castFunPtrToPtr imported_llvmexception),
                                                                          ("llvmdebugmsg", castFunPtrToPtr imported_llvmdebugmsg),
                                                                          ("llvmRegisterAlloc", castFunPtrToPtr imported_llvmRegisterAlloc),
                                                                          ("llvmRegisterFree", castFunPtrToPtr imported_llvmRegisterFree)
                                                                        ]
                                                    ; _ <- mapM (\ (fctname, fctptr) -> registerRunTime mod engine fctname fctptr) runtime_fct
                                                    ; return engine
                                                    }
                           )
                         }

getModuleInterp :: LLVMModule -> IO (ExecutionEngineRef)
getModuleInterp mod = do { modprov <- LLVM.createModuleProviderForExistingModule mod
                         ; (alloca $ \ eePtr ->
                                alloca $ \errPtr -> do {
                                                    ; engine <- do {
                                                                ; ret <- Engine.createInterpreter eePtr modprov errPtr
                                                                --; ret <- Engine.createInterpreter eePtr modprov errPtr
                                                                ; if ret == 1 then do err <- peek errPtr
                                                                                      errStr <- peekCString err
                                                                                      free err
                                                                                      ioError . userError $ errStr
                                                                  else
                                                                      peek eePtr
                                                                }
                                                    -- here we install by hand some runtime function ()
                                                    -- addGlobalMapping :: ExecutionEngineRef -> ValueRef -> Ptr () -> IO ()
                                                    -- function only add if requested ...

                                                    ; let runtime_fct = [ ("llvmexception", castFunPtrToPtr imported_llvmexception),
                                                                          ("llvmdebugmsg", castFunPtrToPtr imported_llvmdebugmsg),
                                                                          ("llvmRegisterAlloc", castFunPtrToPtr imported_llvmRegisterAlloc),
                                                                          ("llvmRegisterFree", castFunPtrToPtr imported_llvmRegisterFree)
                                                                        ]
                                                    ; _ <- mapM (\ (fctname, fctptr) -> registerRunTime mod engine fctname fctptr) runtime_fct
                                                    ; return engine
                                                    }
                           )
                         }



runFunction :: ExecutionEngineRef -> LLVMFunction -> [Engine.GenericValueRef] -> IO Engine.GenericValueRef
runFunction engine fct args | isaLLVMFct fct = withArrayLen args $ \ len ptr -> Engine.runFunction engine (valOf fct) (fromIntegral len) ptr
                            | otherwise = error $ "runFunction: not a function, " ++ show fct

optimizeModule :: LLVMModule -> IO ()
optimizeModule mod = do {
  ; passmanager <- LLVM.createPassManager
  ; _ <- Optim.addArgumentPromotionPass passmanager
  ; _ <- Optim.addConstantMergePass passmanager
  ; _ <- Optim.addDeadArgEliminationPass passmanager
  ; _ <- Optim.addDeadTypeEliminationPass passmanager
  ; _ <- Optim.addFunctionAttrsPass passmanager
  ; _ <- Optim.addFunctionInliningPass passmanager
  ; _ <- Optim.addGlobalDCEPass passmanager
  ; _ <- Optim.addGlobalOptimizerPass passmanager
  ; _ <- Optim.addIPConstantPropagationPass passmanager
  ; _ <- Optim.addLowerSetJmpPass passmanager
  ; _ <- Optim.addPruneEHPass passmanager
  ; _ <- Optim.addRaiseAllocationsPass passmanager
  ; _ <- Optim.addStripDeadPrototypesPass passmanager
  ; _ <- Optim.addStripSymbolsPass passmanager
  ; _ <- Optim.addCFGSimplificationPass passmanager
  ; _ <- Optim.addConstantPropagationPass passmanager
  ; _ <- Optim.addDemoteMemoryToRegisterPass passmanager
  ; _ <- Optim.addGVNPass passmanager
  ; _ <- Optim.addInstructionCombiningPass passmanager
  ; _ <- Optim.addPromoteMemoryToRegisterPass passmanager
  ; _ <- Optim.addReassociatePass passmanager
  ; _ <- Optim.addAggressiveDCEPass passmanager
  ; _ <- Optim.addDeadStoreEliminationPass passmanager
  ; _ <- Optim.addIndVarSimplifyPass passmanager
  ; _ <- Optim.addJumpThreadingPass passmanager
  ; _ <- Optim.addLICMPass passmanager
  ; _ <- Optim.addLoopDeletionPass passmanager
  --; _ <- Optim.addLoopIndexSplitPass passmanager
  ; _ <- Optim.addLoopRotatePass passmanager
  ; _ <- Optim.addLoopUnrollPass passmanager
  ; _ <- Optim.addLoopUnswitchPass passmanager
  ; _ <- Optim.addMemCpyOptPass passmanager
  ; _ <- Optim.addSCCPPass passmanager
  ; _ <- Optim.addScalarReplAggregatesPass passmanager
  ; _ <- Optim.addSimplifyLibCallsPass passmanager
  ; _ <- Optim.addTailCallEliminationPass passmanager

         -- optimize the module
  ; _ <- LLVM.runPassManager passmanager mod
  ; return ()
  }

optimizeFunction :: LLVMValue -> IO ()
optimizeFunction fct = do {
  
  ; mod <- liftIO $ LLVM.getGlobalParent $ valOf fct
  ; modp <- LLVM.createModuleProviderForExistingModule mod
  ; passmanager <- LLVM.createFunctionPassManager modp                   
                   
  -- do not want this one                 
  -- ; _ <- Optim.addDemoteMemoryToRegisterPass passmanager

  ; _ <- Optim.addConstantPropagationPass passmanager                   
         
  ; _ <- Optim.addGVNPass passmanager
                   
  -- this one generate an strange error at runtime                 
  --; _ <- Optim.addInstructionCombiningPass passmanager                   
                   
  ; _ <- Optim.addPromoteMemoryToRegisterPass passmanager
  ; _ <- Optim.addReassociatePass passmanager
  ; _ <- Optim.addAggressiveDCEPass passmanager

                   
  ; _ <- Optim.addDeadStoreEliminationPass passmanager
  ; _ <- Optim.addIndVarSimplifyPass passmanager
  ; _ <- Optim.addLICMPass passmanager
  ; _ <- Optim.addLoopDeletionPass passmanager
  --; _ <- Optim.addLoopIndexSplitPass passmanager

  ; _ <- Optim.addLoopRotatePass passmanager
  ; _ <- Optim.addLoopUnrollPass passmanager
  ; _ <- Optim.addLoopUnswitchPass passmanager
  ; _ <- Optim.addMemCpyOptPass passmanager
  ; _ <- Optim.addSCCPPass passmanager
  ; _ <- Optim.addScalarReplAggregatesPass passmanager
  ; _ <- Optim.addSimplifyLibCallsPass passmanager
  ; _ <- Optim.addTailCallEliminationPass passmanager
  ; _ <- Optim.addCFGSimplificationPass passmanager
  ; _ <- Optim.addJumpThreadingPass passmanager

  -- optimize the function
  ; _ <- LLVM.initializeFunctionPassManager passmanager
  ; _ <- LLVM.runFunctionPassManager passmanager $ valOf fct
  ; _ <- LLVM.finalizeFunctionPassManager passmanager
  --; putTraceMsg "step4"         
    
  ; return ()
  }

-- higher level LLVM CodeGen

-- need the simple forloop

buildForLoop :: LLVMBuilder {- the current builder -} -> LLVMValue {- the initial value -}
                -> (LLVMBuilder -> LLVMValue {- the current value-} -> IO LLVMValue {- test result -} ) {- the test, true => we end the loop -}
                -> (LLVMBuilder -> LLVMValue {- the current value-} -> IO LLVMValue {- the next value -} ) {- the body -}
                -> IO ()

buildForLoop builder init test body = do {
  ; let ty = typeOf init
  -- we grab the current function and block
  ; curb <- getParentBlock builder
  -- we first create all the block we will need
  ; testb <- createBlock builder "for_loop_test"
  ; bodyb <- createBlock builder "for_loop_body"
  ; endb <- createBlock builder "for_loop_end"
  -- we jump the the test block, which begin by a phi (either comming from the initial value or next value)
  ; _ <- buildBr builder testb
  ; moveBuilder builder testb
  ; val <- buildPhi builder ty
  -- perform the test
  ; testres <- test builder val
  -- perform the conditional jump
  ; _ <- buildCondBr builder testres endb bodyb
  -- we build the body, the value is entered from testb
  ; moveBuilder builder bodyb
  ; bval <- buildPhi builder ty
  ; addIncoming bval [(val, testb)]
  -- run the loop body
  ; newval <- body builder bval
  ; bodyendb <- getParentBlock builder
  -- jump back to test, and add this incoming
  ; _<- buildBr builder testb
  ; addIncoming val [(init, curb), (newval, bodyendb)]
  -- finally move to the end block
  ; moveBuilder builder endb
  ; return ()
  }

-- just as previous but incrementing an i32 until a value
buildCounterLoop :: LLVMBuilder -> LLVMValue {- init -} -> LLVMValue {- stop -} -> (LLVMBuilder -> LLVMValue -> IO () {- action -}) -> IO ()
buildCounterLoop builder init stopval action = do {
  ; let test = \ builder val -> do {
          ; test <- buildICmp builder IUGE val stopval
          ; return test
          }
  ; let body = \ builder val -> do {
          ; action builder val
          ; let inc = integer2LLVMInteger 1 32
          ; res <- buildAdd builder inc val
          ; return res
          }
  ; buildForLoop builder init test body
  }

-- build a ifthenelse
buildIfThenElse :: LLVMBuilder -> (LLVMBuilder -> IO LLVMValue) {- test -} -> (LLVMBuilder -> IO LLVMValue) {- then -} -> (LLVMBuilder -> IO LLVMValue) {- else -} -> IO LLVMValue {- result -}
buildIfThenElse builder test thencase elsecase = do {
  -- do the test and switch
  ; testres <- test builder
  ; thenb <- createBlock builder "thenb"
  ; elseb <- createBlock builder "elseb"
  ; endb <- createBlock builder "ifthenelseed"
  ; buildCondBr builder testres thenb elseb
  -- both branches
  ; moveBuilder builder thenb
  ; res1 <- thencase builder
  ; buildBr builder endb
  ; moveBuilder builder elseb
  ; res2 <- elsecase builder
  ; buildBr builder endb
  ; moveBuilder builder endb
  -- the final block
  ; res <- buildPhi builder $ typeOf res1
  ; addIncoming res [(res1, thenb), (res2, elseb)]
  ; return res
  }

-- same but without returned values
buildIfThenElse2 :: LLVMBuilder -> (LLVMBuilder -> IO LLVMValue) {- test -} -> (LLVMBuilder -> IO ()) {- then -} -> (LLVMBuilder -> IO ()) {- else -} -> IO () {- result -}
buildIfThenElse2 builder test thencase elsecase = do {
  -- do the test and switch
  ; testres <- test builder
  ; thenb <- createBlock builder "thenb"
  ; elseb <- createBlock builder "elseb"
  ; endb <- createBlock builder "ifthenelseed"
  ; buildCondBr builder testres thenb elseb
  -- both branches
  ; moveBuilder builder thenb
  ; thencase builder
  ; buildBr builder endb
  ; moveBuilder builder elseb
  ; elsecase builder
  ; buildBr builder endb
  ; moveBuilder builder endb
  -- the final block
  ; return ()
  }


-- initialization of data

initData :: LLVMBuilder -> LLVMValue {- :: ty* -} -> IO ()

initData builder ptr = do {
  ; let TDerived (TPointer ty) = typeOf ptr
  ; val <- constNull ty
  ; _ <- buildStore builder val ptr
  ; return ()
  }

-- Several function for Managed Type

-- increment counter
incRef :: LLVMBuilder -> LLVMValue {- :: managed value  -} -> IO ()
incRef builder val = do {
  ; let fctty = fctType [typeOf val] voidType
  ; let fctname = "incRef_" ++ show (typeOf val)
  ; let codegen = incRef'      
  ; res <- cachedApplication builder fctname fctty codegen [val]
  ; return ()
  }

incRef' :: LLVMBuilder -> [LLVMValue] -> IO (Maybe LLVMValue)
incRef' builder [ptr] = do {
                        -- test if the manage value is null and build branches
                        ; buildIfThenElse2 builder
                                               (\ builder -> buildIsNull builder $ typeCast ptr $ ptrType int8Type)
                                               (\ builder -> return ())
                                               (\ builder -> do {
                                                             ; let managedp = (case rollUp $ typeOf ptr of
                                                                                 TManaged (TDynArray ty) -> typeCast ptr $ ptrType $ dynDArrayType ty
                                                                                 TManaged (TGCed ty) -> typeCast ptr $ ptrType $ gcedDType ty
                                                                                 TManaged (TSum tys) -> typeCast ptr $ ptrType $ sumDType tys
                                                                                 TManaged (TClosure tys) -> typeCast ptr $ ptrType $ closureDType tys
                                                                                 TManaged (TStack ty) -> typeCast ptr $ ptrType $ stackDType ty
                                                                                 TManaged (TFinalizer ty) -> typeCast ptr $ ptrType $ finalizerDType ty
                                                                                 ty -> error $ "incRef': not a managed type, " ++ show ptr
                                                                              )
                                                             ; counterp <- buildStructGEP builder managedp 0
                                                             ; counterval <- buildLoad builder counterp
                                                             ; newcounterval <- buildAdd builder counterval (integer2LLVMInteger 1 32)
                                                             ; buildStore builder newcounterval counterp
                                                             }
                                               )
                        ; return Nothing
                        }

decRef :: LLVMBuilder -> LLVMValue {- :: managed value -} -> IO ()
decRef builder val = do {
                     ; let fctty = fctType [typeOf val] voidType
                     ; let fctname = "incRef_" ++ show (typeOf val)
                     ; let codegen = incRef'      
                     ; res <- cachedApplication builder fctname fctty codegen [val]
                     ; return ()
                     }

decRef' :: LLVMBuilder -> [LLVMValue] -> IO (Maybe LLVMValue)                     
decRef' builder [ptr] =  do {
                       -- test if the managed is null and build branches
                       ; buildIfThenElse2 builder
                                              (\ builder -> buildIsNull builder $ typeCast ptr $ ptrType int8Type)
                                              (\ builder -> return ())
                                              (\ builder -> do {
                                                            ; let managedp = (case rollUp $ typeOf ptr of
                                                                                TManaged (TDynArray ty) -> typeCast ptr $ ptrType $ dynDArrayType ty
                                                                                TManaged (TGCed ty) -> typeCast ptr $ ptrType $ gcedDType ty
                                                                                TManaged (TSum tys) -> typeCast ptr $ ptrType $ sumDType tys
                                                                                TManaged (TClosure tys) -> typeCast ptr $ ptrType $ closureDType tys
                                                                                TManaged (TStack ty) -> typeCast ptr $ ptrType $ stackDType ty
                                                                                TManaged (TFinalizer ty) -> typeCast ptr $ ptrType $ finalizerDType ty
                                                                                ty -> error $ "decRef': not a managed type, " ++ show ptr
                                                                             )
                                                            ; counterp <- buildStructGEP builder managedp 0
                                                            ; counterval <- buildLoad builder counterp
                                                            -- this second test is to now if we need to deallocate the data
                                                            ; buildIfThenElse2 builder
                                                                                   (\ builder -> buildICmp builder IULE counterval (integer2LLVMInteger 1 32))
                                                                                   -- deallocate
                                                                                   (\ builder -> do {
                                                                                                 ; destroyManagedType builder ptr
                                                                                                 }
                                                                                   )
                                                                                   -- decrement the counter
                                                                                   ( \ builder -> do {
                                                                                                  ; newcounterval <- buildSub builder counterval (integer2LLVMInteger 1 32)
                                                                                                  ; buildStore builder newcounterval counterp
                                                                                                  }
                                                                                   )
                                                            }
                                              )
                       ; return Nothing
                       }

-- TODO: change this into a function codegen / call (as incRef)
destroyManagedType :: LLVMBuilder -> LLVMValue {- :: managed value -} -> IO ()
destroyManagedType builder val = do {
                     ; let fctty = fctType [typeOf val] voidType
                     ; let fctname = "destroyManagedType_" ++ show (typeOf val)
                     ; let codegen = destroyManagedType'      
                     ; res <- cachedApplication builder fctname fctty codegen [val]
                     ; return ()
                     }

destroyManagedType' :: LLVMBuilder -> [LLVMValue] {- :: (managed ...) -} -> IO (Maybe LLVMValue)
destroyManagedType' builder [ptr] | TManaged (TDynArray ty) <- rollUp $ typeOf ptr = do {

                                                                                     ; when debugGC $ buildDebugMsg builder $ "destroyManagedType: " ++ show ptr

                                                                                     ; let ptr' = typeCast ptr $ ptrType $ dynDArrayType ty
                                                                                     -- we need to do a for loop over all the possible index, calling each time mutateRefFirstLevel
                                                                                     ; sizep <- buildStructGEP builder ptr' 1
                                                                                     ; size <- buildLoad builder sizep

                                                                                     ; datap <- buildStructGEP builder ptr' 2
                                                                                     ; buildCounterLoop builder (integer2LLVMInteger 0 32) size (\ builder val -> do {

                                                                                                                                                                  ; when debugGC $ buildDebugMsg builder $ "array elt ... "

                                                                                                                                                                  ; ptr <- buildGEP builder datap [(integer2LLVMInteger 0 32), val]
                                                                                                                                                                  ; mutateRefFirstLevel builder ptr False

                                                                                                                                                                  }
                                                                                                                                                )
                                                                                     -- then we free
                                                                                     ; buildFree builder ptr'
                                                                                     ; return Nothing
                                                                                     }
                                  | TManaged (TGCed ty) <- rollUp $ typeOf ptr = do {

                                                                                 ; when debugGC $ buildDebugMsg builder $ "destroyManagedType: " ++ show ptr

                                                                                 ; let ptr' = typeCast ptr $ ptrType $ gcedDType ty
                                                                                 ; datap <- buildStructGEP builder ptr' 1
                                                                                 ; mutateRefFirstLevel builder datap False
                                                                                 -- then we free
                                                                                 ; buildFree builder ptr'
                                                                                 ; return Nothing
                                                                                 }
                                  | TManaged (TSum tys) <- rollUp $ typeOf ptr = do {

                                                                                 ; when debugGC $ buildDebugMsg builder $ "destroyManagedType: " ++ show ptr

                                                                                 ; let ptr' = typeCast ptr $ ptrType $ sumDType tys
                                                                                 ; indexp <- buildStructGEP builder ptr' 1
                                                                                 ; indexval <- buildLoad builder indexp

                                                                                 --

                                                                                 ; caseblocks <- mapM (\ i -> createBlock builder $ "case_" ++ show i) [0..(length tys - 1)]
                                                                                 ; endblock <- createBlock builder "end_block"
                                                                                 ; errorblock <- createBlock builder "error_block"
                                                                                 ; buildSwitch builder indexval (zip (map (flip integer2LLVMInteger 32 . fromIntegral) [0..(length tys - 1)]) caseblocks) errorblock

                                                                                 ; moveBuilder builder errorblock
                                                                                 ; buildException2 builder ("wrong tag for type: " ++ show (rollUp $ typeOf ptr))

                                                                                 ; _ <- mapM (\ (b, i) -> do {
                                                                                                          ; moveBuilder builder b
                                                                                                          ; datap <- buildStructGEP builder ptr' 2
                                                                                                          ; datap' <- buildBitCast builder datap $ ptrType $ tys!!i
                                                                                                          ; mutateRefFirstLevel builder datap' False
                                                                                                          ; buildBr builder endblock
                                                                                                          }) $ zip caseblocks [0..(length tys - 1)]
                                                                                 ; moveBuilder builder endblock
                                                                                 ; buildFree builder ptr'
                                                                                 ; return Nothing
                                                                                 }
                                  | TManaged (TStack ty) <- rollUp $ typeOf ptr = do {

                                                                                  ; when debugGC $ buildDebugMsg builder $ "destroyManagedType: " ++ show ptr

                                                                                  ; let ptr' = typeCast ptr $ ptrType $ stackDType ty
                                                                                  -- we need to do a for loop over all the possible index, calling each time mutateRefFirstLevel
                                                                                  ; sizep <- buildStructGEP builder ptr' 2
                                                                                  ; size <- buildLoad builder sizep
                                                                                  ; datapp <- buildStructGEP builder ptr' 3
                                                                                  ; datap <- buildLoad builder datapp
                                                                                  ; buildCounterLoop builder (integer2LLVMInteger 0 32) size (\ builder val -> do {
                                                                                                                                                               ; ptr <- buildGEP builder datap [(integer2LLVMInteger 0 32), val]
                                                                                                                                                               ; mutateRefFirstLevel builder ptr False
                                                                                                                                                               }
                                                                                                                                             )
                                                                                  -- then we free
                                                                                  ; buildFree builder datap
                                                                                  ; buildFree builder ptr'
                                                                                  ; return Nothing
                                                                                  }
                                  | TManaged (TFinalizer ty) <- rollUp $ typeOf ptr = do {
                                                                                      ; let ptr' = typeCast ptr $ ptrType $ finalizerDType ty
                                                                                      -- grab the function & the data
                                                                                      ; fctp <- buildStructGEP builder ptr' 2
                                                                                      ; fct <- buildLoad builder fctp
                                                                                               
                                                                                      ; mdatap <- buildStructGEP builder ptr' 1
                                                                                      ; mdata <- buildLoad builder mdatap
                                                                                                 
                                                                                      -- apply
                                                                                      ; _ <- buildCall builder fct [mdata]
                                                                                             
                                                                                      -- free
                                                                                      ; buildFree builder ptr'
                                                                                                  
                                                                                      ; return Nothing 
                                                                                      }

                                  | TManaged (TClosure tys) <- rollUp $ typeOf ptr = do {
                                                                                     ; destroyClosure builder ptr

                                                                                     ; let ptr' = typeCast ptr $ ptrType $ closureDType tys

                                                                                     ; buildFree builder ptr'
                                                                                     ; return Nothing 
                                                                                     }
                                                               

                                  | otherwise = error $ "destroyManagedType: not a managed type, " ++ show (typeOf ptr)

getRefCount :: LLVMBuilder -> LLVMValue -> IO LLVMValue
getRefCount builder ptr = do {
  ; let fctty = fctType [typeOf ptr] int32Type
  ; let fctname = "getRefCount_" ++ show (typeOf ptr)
  ; let codegen = getRefCount'
  ; res <- cachedApplication builder fctname fctty codegen [ptr]
  ; return res
  }

getRefCount' :: LLVMBuilder -> [LLVMValue] -> IO (Maybe LLVMValue)
getRefCount' builder [ptr] = do {
  ; let managedp = (case rollUp $ typeOf ptr of
                       TManaged (TDynArray ty) -> typeCast ptr $ ptrType $ dynDArrayType ty
                       TManaged (TGCed ty) -> typeCast ptr $ ptrType $ gcedDType ty
                       TManaged (TSum tys) -> typeCast ptr $ ptrType $ sumDType tys
                       TManaged (TClosure tys) -> typeCast ptr $ ptrType $ closureDType tys
                       TManaged (TStack ty) -> typeCast ptr $ ptrType $ stackDType ty
                       TManaged (TFinalizer ty) -> typeCast ptr $ ptrType $ finalizerDType ty
                       ty -> error $ "incRef': not a managed type, " ++ show ptr
                   )
  ; counterp <- buildStructGEP builder managedp 0
  ; counterval <- buildLoad builder counterp
  ; return $ Just counterval        
  }

mutateRefFirstLevel :: LLVMBuilder -> LLVMValue {- :: ty* -} -> Bool {- True: increment | False: decrement -} -> IO ()
mutateRefFirstLevel builder ptr direction = do {
  ; let fctname = "mutateRefFirstLevel_" ++ show (typeOf ptr) ++ "_" ++ show direction
  ; let fctty = fctType [typeOf ptr] voidType
  ; let codegen = \ builder [ptr] -> do { mutateRefFirstLevel' builder ptr direction
                                        ; return Nothing
                                        }
  ; _ <- cachedApplication builder fctname fctty codegen [ptr]
  ; return ()
  }

mutateRefFirstLevel' :: LLVMBuilder -> LLVMValue {- :: ty* -} -> Bool {- True: increment | False: decrement -} -> IO ()
mutateRefFirstLevel' builder ptr direction | TDerived (TPointer (TManaged (TDynArray ty))) <- rollUp $ typeOf ptr = do { when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr; ptr' <- buildLoad builder ptr; (if direction then incRef else decRef) builder ptr'}
                                                                                                                           | TDerived (TPointer (TManaged (TGCed ty))) <- rollUp $ typeOf ptr = do { when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr;ptr' <- buildLoad builder ptr; (if direction then incRef else decRef) builder ptr'}
                                                                                                                                                                                                       | TDerived (TPointer (TManaged (TSum tys))) <- rollUp $ typeOf ptr = do { when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr;ptr' <- buildLoad builder ptr; (if direction then incRef else decRef) builder ptr'}
                                                                                                                                                                                                                                                                                   | TDerived (TPointer (TManaged (TStack tys))) <- rollUp $ typeOf ptr = do { when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr;ptr' <- buildLoad builder ptr; (if direction then incRef else decRef) builder ptr'}
                                                                                                                                                                                                                                                                                                                                                                 | TDerived (TPointer (TManaged (TClosure tys))) <- rollUp $ typeOf ptr = do { when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr;ptr' <- buildLoad builder ptr; (if direction then incRef else decRef) builder ptr'}
                                                                                                                                                                                                                                                                                                                                                                                                                                                 | TDerived (TPointer (TManaged (TFinalizer ty))) <- rollUp $ typeOf ptr = do { when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr;ptr' <- buildLoad builder ptr; (if direction then incRef else decRef) builder ptr'}
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | TDerived (TPointer (TDerived (TAggregate (TArray sz ty)))) <- rollUp $ typeOf ptr = do {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        ; when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        ; _ <- mapM (\ i -> do {

                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            ; ptr' <- buildGEP builder ptr [(integer2LLVMInteger 0 32), (integer2LLVMInteger i 32)]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            ; mutateRefFirstLevel builder ptr' direction
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            }
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ) [0..(fromIntegral sz -1)]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        ; return ()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | TDerived (TPointer (TDerived (TAggregate (TStructure tys)))) <- rollUp $ typeOf ptr = do {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          ; when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          ; _ <- mapM (\ i -> do {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              ; ptr' <- buildStructGEP builder ptr $ fromIntegral i
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              ; mutateRefFirstLevel builder ptr' direction
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              }
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      ) [0..(length tys -1)]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          ; return ()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | TDerived (TPointer (TDerived (TAggregate (TPackedStructure tys)))) <- rollUp $ typeOf ptr = do {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                ; when debugGC $ buildDebugMsg builder $ "mutateRefFirstLevel: " ++ show ptr
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                ; _ <- mapM (\ i -> do {
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ; ptr' <- buildStructGEP builder ptr $ fromIntegral i
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    ; mutateRefFirstLevel builder ptr' direction
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    }
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            ) [0..(length tys -1)]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                ; return ()
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | TDerived (TPointer ty@(TRecType (TDef _ _))) <- rollUp $ typeOf ptr = mutateRefFirstLevel builder (typeCast ptr $ TDerived $ TPointer $ rollUp ty) direction
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | otherwise = return ()

-- creation / lookup / mutation / ... from managed type
-- N.B.: not really harmonized .. sometimes lookup returns ty, sometimes ty* .... where is the logic ?

-- specific function for dynamic array
createDynArray :: LLVMBuilder -> LLVMType {- = ty -} -> LLVMValue {- = size -} -> IO LLVMValue {- :: (dynArrayType ty) -}
createDynArray builder ty sz = do {
  ; let fctname = "createDynArray_" ++ show ty
  ; let fctty = fctType [int32Type] $ dynArrayType ty
  ; let codegen = \ builder [sz] -> do { res <- createDynArray' builder ty sz
                                       ; return $ Just res
                                       }
  ; res <- cachedApplication builder fctname fctty codegen [sz]
  ; return res
  }


createDynArray' :: LLVMBuilder -> LLVMType {- = ty -} -> LLVMValue {- = size -} -> IO LLVMValue {- :: (dynArrayType ty) -}
createDynArray' builder ty sz | isaInt sz = do {
                                            -- compute the size of the allocation
                                            ; nullp <- constNull $ ptrType $ dynDArrayType ty
                                            ; datasz <- buildGEP builder nullp [(integer2LLVMInteger 0 32), (integer2LLVMInteger 2 32), sz]

                                            ; sz' <- buildPtrToInt builder datasz int64Type
                                            ; sz' <- buildIntCast builder sz' int32Type False

                                            -- we allocate the memory
                                            --; buildPrintf builder ("createDynArray :: " ++ show ty ++ ", of size %d, memory size: %d \n") [sz, sz']

                                            ; ptr <- buildAlloc2 builder sz' $ dynDArrayType ty

                                            -- initialize the counter to 1
                                            ; counterp <- buildStructGEP builder ptr 0
                                            ; buildStore builder (integer2LLVMInteger 1 32) counterp
                                            -- initialize the size
                                            ; sizep <- buildStructGEP builder ptr 1
                                            ; buildStore builder sz sizep
                                            -- we initialize the data values
                                            ; datap <- buildStructGEP builder ptr 2
                                            ; buildCounterLoop builder (integer2LLVMInteger 0 32) sz (\ builder val -> do {
                                                                                                                       ; ptr <- buildGEP builder datap [(integer2LLVMInteger 0 32), val]
                                                                                                                       ; initData builder ptr
                                                                                                                       }
                                                                                                     )
                                            ; return $ LLVMValue (valOf ptr) $ dynArrayType ty
                                            }
                              | otherwise = error $ "createDynArray: not a size, " ++ show sz

lookupDynArray :: LLVMBuilder -> LLVMValue {- = index -} -> LLVMValue {- :: (dynArray ty) -} -> IO LLVMValue {- :: ty* -}
lookupDynArray builder index dynarray = do {
  ; let fctname = "lookupDynArray_" ++ show (typeOf dynarray)
  ; let fctty = fctType [typeOf dynarray, int32Type] $ ptrType $ dynArrayEltTy $ typeOf dynarray
  ; let codegen = \ builder [dynarray, index] -> do { res <- lookupDynArray' builder index dynarray
                                                    ; return $ Just res 
                                                    }
  ; res <- cachedApplication builder fctname fctty codegen [dynarray, index]
  ; return res
  }

lookupDynArray' :: LLVMBuilder -> LLVMValue {- = index -} -> LLVMValue {- :: (dynArray ty) -} -> IO LLVMValue {- :: ty* -}
lookupDynArray' builder index dynarray = do {
                                         -- nb: should we test that it's not nullptr ??
                                         ; let ty' = dynArrayEltTy $ typeOf dynarray
                                         ; let dynarray' = typeCast dynarray $ ptrType $ dynDArrayType ty'
                                         ; datap <- buildStructGEP builder dynarray' 2
                                         ; eltp <- buildGEP builder datap [(integer2LLVMInteger 0 32), index]
                                         ; return eltp
                                         }

mutateDynArray :: LLVMBuilder -> LLVMValue {- = index -} -> LLVMValue {- :: ty -} -> LLVMValue {- :: (dynArrayType ty) -} -> IO ()
mutateDynArray builder index val dynarray = do {
  ; let fctname = "mutateDynArray_" ++ show (typeOf dynarray)
  ; let fctty = fctType [int32Type, dynArrayEltTy $ typeOf dynarray, typeOf dynarray] voidType
  ; let codegen = \ builder [index, val, dynarray] -> do { mutateDynArray' builder index val dynarray
                                                         ; return Nothing
                                                         }
  ; _ <- cachedApplication builder fctname fctty codegen [index, val, dynarray]
  ; return ()
  }  

mutateDynArray' :: LLVMBuilder -> LLVMValue {- = index -} -> LLVMValue {- :: ty -} -> LLVMValue {- :: (dynArrayType ty) -} -> IO ()
mutateDynArray' builder index val dynarray = do {
                                             -- nb: should we test that it's not nullptr ??
                                             ; let ty' = dynArrayEltTy $ typeOf dynarray
                                             ; let dynarray' = typeCast dynarray $ ptrType $ dynDArrayType ty'
                                             ; datap <- buildStructGEP builder dynarray' 2
                                             ; eltp <- buildGEP builder datap [(integer2LLVMInteger 0 32), index]
                                             ; buildStore builder val eltp
                                             ; return ()
                                             }

dynArraySize :: LLVMBuilder -> LLVMValue {- :: (dynArrayType ty) -} -> IO LLVMValue {- size -}
dynArraySize builder dynarray = do {
  ; let fctname = "dynArraySize_" ++ show (typeOf dynarray)
  ; let fctty = fctType [typeOf dynarray] int32Type
  ; let codegen = \ builder [dynarray] -> do { res <- dynArraySize' builder dynarray
                                             ; return $ Just res
                                             }
  ; res <- cachedApplication builder fctname fctty codegen [dynarray]
  ; return res
  }  

dynArraySize' :: LLVMBuilder -> LLVMValue {- :: (dynArrayType ty) -} -> IO LLVMValue {- size -}
dynArraySize' builder array = do {
                              ; let ty' = dynArrayEltTy $ typeOf array
                              ; let array' = typeCast array $ ptrType $ dynDArrayType ty'
                              ; sizep <- buildStructGEP builder array' 1
                              ; size <- buildLoad builder sizep
                              ; return size
                              }

copyExtDynArray :: LLVMBuilder -> LLVMValue {- :: dynArrayType ty-} -> LLVMValue {- :: int32Type -} -> IO LLVMValue {- :: dynArrayType ty -}
copyExtDynArray builder dynarray extsize = do {
  ; let fctname = "copyExtDynArray_" ++ show (typeOf dynarray)
  ; let fctty = fctType [typeOf dynarray, int32Type] $ typeOf dynarray
  ; let codegen = \ builder [dynarray, extsize] -> do { res <- copyExtDynArray' builder dynarray extsize
                                                      ; return $ Just res
                                             }
  ; res <- cachedApplication builder fctname fctty codegen [dynarray, extsize]
  ; return res    
  }

copyExtDynArray' :: LLVMBuilder -> LLVMValue {- :: dynArrayType ty-} -> LLVMValue {- :: int32Type -} -> IO LLVMValue {- :: dynArrayType ty -}
copyExtDynArray' builder array extsize = do {
                                         ; let ty' = dynArrayEltTy $ typeOf array
                                         ; let array' = typeCast array $ ptrType $ dynDArrayType ty'
                                         ; sizep <- buildStructGEP builder array' 1
                                         ; size <- buildLoad builder sizep
                                         ; datap <- buildStructGEP builder array' 2
                                                    
                                         -- the new array
                                         ; newsize <- buildAdd builder size extsize
                                         ; newarray <- createDynArray builder ty' newsize
                                         ; let newarray' = typeCast newarray $ ptrType $ dynDArrayType ty'
                                         ; newdatap <- buildStructGEP builder newarray' 2
                                                       
                                         -- the copy loop
                                         ; buildCounterLoop builder
                                                                (integer2LLVMInteger 0 32)
                                                                size
                                                                (\ builder val -> do {
                                                                                  ; mdatap <- buildGEP builder datap [integer2LLVMInteger 0 32, val]
                                                                                  ; mutateRefFirstLevel builder mdatap True
                                                                                  ; mdata <- buildLoad builder mdatap
                                                                                  ; mnewdatap <- buildGEP builder newdatap [integer2LLVMInteger 0 32, val]
                                                                                  ; buildStore builder mdata mnewdatap
                                                                                  }
                                                                )
                                         ; return newarray
                                                  
                                         }

-- specific functions for GCed Value
createGCed :: LLVMBuilder -> LLVMType {- = ty -} -> IO LLVMValue {- :: gcedType ty -}
createGCed builder ty = do {
  ; let fctname = "createGCed_" ++ show ty
  ; let fctty = fctType [] $ gcedType ty  
  ; let codegen = \ builder [] -> do { res <- createGCed' builder ty
                                     ; return $ Just res
                                     }
  ; res <- cachedApplication builder fctname fctty codegen []
  ; return res    
  }


createGCed' :: LLVMBuilder -> LLVMType {- = ty -} -> IO LLVMValue {- :: gcedType ty -}
createGCed' builder ty = do {
                         -- compute the type of the allocation
                         ; let ty' = gcedDType ty
                         -- allocate the needed space
                         ; ptr <- buildAlloc builder ty'
                         -- we initialize the counter to 1
                         ; counterp <- buildStructGEP builder ptr 0
                         ; _ <- buildStore builder (integer2LLVMInteger 1 32) counterp
                         -- we initialize the data values
                         ; datap <- buildStructGEP builder ptr 1
                         ; initData builder datap
                         -- return the pointer
                         ; return $ LLVMValue (valOf ptr) $ gcedType ty
                         }

-- grab the GCed Value Data
getGCedData :: LLVMBuilder -> LLVMValue {- :: gcedType ty -} -> IO LLVMValue {- :: ty* -}
getGCedData builder ptr = do {
  ; let ty' = gcedEltTy $ typeOf ptr
  ; let fctname = "getGCedData_" ++ show ty'
  ; let fctty = fctType [typeOf ptr] $ ptrType ty'  
  ; let codegen = \ builder [ptr] -> do { res <- getGCedData' builder ptr
                                        ; return $ Just res
                                        }
  ; res <- cachedApplication builder fctname fctty codegen [ptr]
  ; return res    
  }

getGCedData' :: LLVMBuilder -> LLVMValue {- :: gcedType ty -} -> IO LLVMValue {- :: ty* -}
getGCedData' builder ptr = do {
                           ; let ty' = gcedEltTy $ typeOf ptr
                           ; let ptr' = typeCast ptr $ ptrType $ gcedDType ty'
                           ; datap <- buildStructGEP builder ptr' 1
                           ; return datap
                           }
    
-- specific funcion for Sum Type
createSum :: LLVMBuilder -> LLVMType {- = sumType tys -} -> Int {- = i -} -> LLVMValue {- :: tys!!i -} -> IO LLVMValue {- :: sumType tys -}
createSum builder ty index val = do {
  ; let fctname = "createSum_" ++ show ty ++ "_" ++ show index
  ; let fctty = fctType [typeOf val] $ ty
  ; let codegen = \ builder [val] -> do { res <- createSum' builder ty index val
                                        ; return $ Just res
                                        }
  ; res <- cachedApplication builder fctname fctty codegen [val]
  ; return res    
  }

createSum' :: LLVMBuilder -> LLVMType {- = sumType tys -} -> Int {- = i -} -> LLVMValue {- :: tys!!i -} -> IO LLVMValue {- :: sumType tys -}
createSum' builder ty index val = do {
                                  ; let TManaged (TSum tys) = rollUp $ ty
                                  ; let ty' = structType [int32Type, int32Type, tys!!index]
                                  ; ptr <- buildAlloc builder ty'
                                           
                                  ; counterp <- buildStructGEP builder ptr 0
                                  ; _ <- buildStore builder (integer2LLVMInteger 1 32) counterp
                                         
                                  ; indexp <- buildStructGEP builder ptr 1
                                  ; _ <- buildStore builder (integer2LLVMInteger (fromIntegral index) 32) indexp
                                         
                                  ; datap <- buildStructGEP builder ptr 2
                                  ; buildStore builder val datap
                                               
                                  ; ptr' <- buildBitCast builder ptr $ sumType tys
                                           
                                  ; return ptr'
                                           
                                  }

createSum2 :: LLVMBuilder -> LLVMType {- = sumType tys -} -> Int {- = i -} -> IO LLVMValue {- :: sumType tys -}
createSum2 builder ty index = do {
  ; let fctname = "createSum2_" ++ show ty ++ "_" ++ show index
  ; let fctty = fctType [] $ ty
  ; let codegen = \ builder [] -> do { res <- createSum2' builder ty index
                                     ; return $ Just res
                                     }
  ; res <- cachedApplication builder fctname fctty codegen []
  ; return res    
}

createSum2' :: LLVMBuilder -> LLVMType {- = sumType tys -} -> Int {- = i -} -> IO LLVMValue {- :: sumType tys -}
createSum2' builder ty index = do {
                               ; let TManaged (TSum tys) = rollUp $ ty
                               ; let ty' = structType [int32Type, int32Type, tys!!index]
                               ; ptr <- buildAlloc builder ty'
                                        
                               ; counterp <- buildStructGEP builder ptr 0
                               ; _ <- buildStore builder (integer2LLVMInteger 1 32) counterp
                                      
                               ; indexp <- buildStructGEP builder ptr 1
                               ; _ <- buildStore builder (integer2LLVMInteger (fromIntegral index) 32) indexp
                                      
                               ; datap <- buildStructGEP builder ptr 2
                               ; initData builder datap
                                          
                               ; ptr' <- buildBitCast builder ptr $ sumType tys
                                         
                               ; return ptr'
                                        
                               }


destructSum :: LLVMBuilder -> LLVMValue {- :: TSum tys -} -> [LLVMBuilder -> LLVMValue {- :: (tys!!n) * -} -> IO LLVMValue] -> IO LLVMValue
destructSum builder val destructors = do {
                                      --; putStrLn "******** phi ***********"

                                      ; let TManaged (TSum tys) = rollUp $ typeOf val
                                      ; let val' = typeCast val $ ptrType $ sumDType tys
                                      ; indexp <- buildStructGEP builder val' 1
                                      ; indexval <- buildLoad builder indexp
                                      ; caseblocks <- mapM (\ i -> createBlock builder $ "case_" ++ show i) [0..(length tys - 1)]
                                      ; endblock <- createBlock builder "end_block"
                                      ; buildSwitch builder indexval (zip (map (flip integer2LLVMInteger 32 . fromIntegral) [0..(length tys - 1)]) caseblocks) endblock
                                      ; origb <- getParentBlock builder
                                      ; results <- mapM (\ (b, i) -> do {
                                                                     ; moveBuilder builder b
                                                                     ; datap <- buildStructGEP builder val' 2
                                                                     ; datap' <- buildBitCast builder datap $ ptrType $ tys!!i
                                                                     ; res <- (destructors!!i) builder datap'

                                                                     -- for debug
                                                                     --; putStrLn $ "case " ++ show i ++ " :: " ++ show (typeOf res)

                                                                     ; buildBr builder endblock
                                                                     ; resb <- getParentBlock builder

                                                                     ; return (res, resb)
                                                                     }) $ zip caseblocks [0..(length tys - 1)]
                                      ; moveBuilder builder endblock
                                      ; let (vals, _) = unzip results
                                      ; res <- buildPhi builder $ typeOf (vals!!0)
                                      ; undef <- getUndef $ typeOf res

                                      -- for debug
                                      --; putStrLn $ "default case :: " ++ show (typeOf res)
                                      --; putStrLn $ "phi :: " ++ show (typeOf res)
                                      --; putStrLn "----------- phi -----------\n\n"


                                      ; addIncoming res ((undef, origb):results)
                                      ; return res
                                      }

-- a special case where the case codegen function are responsible for the continuation
destructSum2 :: LLVMBuilder -> LLVMValue {- :: TSum tys -} -> [LLVMBuilder -> LLVMValue {- :: (tys!!n) * -} -> IO ()] -> IO ()
destructSum2 builder val destructors = do {
                                       --; putStrLn "******** phi ***********"

                                       ; let TManaged (TSum tys) = rollUp $ typeOf val
                                       ; let val' = typeCast val $ ptrType $ sumDType tys
                                       ; indexp <- buildStructGEP builder val' 1
                                       ; indexval <- buildLoad builder indexp
                                       ; caseblocks <- mapM (\ i -> createBlock builder $ "case_" ++ show i) [0..(length tys - 1)]
                                       ; errorblock <- createBlock builder "error_block"
                                       ; buildSwitch builder indexval (zip (map (flip integer2LLVMInteger 32 . fromIntegral) [0..(length tys - 1)]) caseblocks) errorblock
                                       ; origb <- getParentBlock builder
                                       ; mapM (\ (b, i) -> do {
                                                           ; moveBuilder builder b
                                                           ; datap <- buildStructGEP builder val' 2
                                                           ; datap' <- buildBitCast builder datap $ ptrType $ tys!!i
                                                           ; (destructors!!i) builder datap'
                                                           }) $ zip caseblocks [0..(length tys - 1)]
                                       ; moveBuilder builder errorblock
                                       ; buildException2 builder "wrong sum tag"

                                       ; return ()
                                      }

-- a special case where the case codegen function return nothing but converge to the same point
destructSum3 :: LLVMBuilder -> LLVMValue {- :: TSum tys -} -> [LLVMBuilder -> LLVMValue {- :: (tys!!n) * -} -> IO ()] -> IO ()
destructSum3 builder val destructors = do {
                                       --; putStrLn "******** phi ***********"

                                       ; let TManaged (TSum tys) = rollUp $ typeOf val
                                       ; let val' = typeCast val $ ptrType $ sumDType tys
                                       ; indexp <- buildStructGEP builder val' 1
                                       ; indexval <- buildLoad builder indexp
                                       ; caseblocks <- mapM (\ i -> createBlock builder $ "case_" ++ show i) [0..(length tys - 1)]
                                       ; errorblock <- createBlock builder "error_block"
                                       ; endblock <- createBlock builder "end_block"
                                       ; buildSwitch builder indexval (zip (map (flip integer2LLVMInteger 32 . fromIntegral) [0..(length tys - 1)]) caseblocks) errorblock
                                       ; origb <- getParentBlock builder
                                       ; mapM (\ (b, i) -> do {
                                                           ; moveBuilder builder b
                                                           ; datap <- buildStructGEP builder val' 2
                                                           ; datap' <- buildBitCast builder datap $ ptrType $ tys!!i
                                                           ; (destructors!!i) builder datap'
                                                           ; buildBr builder endblock
                                                           }) $ zip caseblocks [0..(length tys - 1)]
                                       ; moveBuilder builder errorblock
                                       ; buildException2 builder "wrong sum tag"

                                       ; moveBuilder builder endblock

                                       ; return ()
                                      }



-- special case of destruction where we are interested in only one case
extractFromSum :: LLVMBuilder -> LLVMValue {- :: TSum tys -} -> Int {- index -} -> IO LLVMValue {- opfully :: (tys!!i)* -}
extractFromSum builder sum index = do {
  ; let TManaged (TSum tys) = rollUp $ typeOf sum
  ; let fctname = "extractFromSum_" ++ show (typeOf sum) ++ "_" ++ show index
  ; let fctty = fctType [typeOf sum] $ ptrType $ tys!!index
  ; let codegen = \ builder [sum] -> do { res <- extractFromSum' builder sum index
                                        ; return $ Just res
                                        }
  ; res <- cachedApplication builder fctname fctty codegen [sum]
  ; return res    
  }

extractFromSum' :: LLVMBuilder -> LLVMValue {- :: TSum tys -} -> Int {- index -} -> IO LLVMValue {- opfully :: (tys!!i)* -}
extractFromSum' builder sum index = do {
                                    ; let TManaged (TSum tys) = rollUp $ typeOf sum
                                    ; let mtype = tys!!index
                                    ; let val' = typeCast sum $ ptrType $ sumDType tys
                                    ; indexp <- buildStructGEP builder val' 1
                                    ; indexval <- buildLoad builder indexp
                                    ; errorblock <- createBlock builder "error_block"
                                    ; extractblock <- createBlock builder "extract_block"
                                    ; test <- buildICmp builder IEQ indexval (integer2LLVMInteger (fromIntegral index) 32)
                                    ; buildCondBr builder test extractblock errorblock

                                    ; moveBuilder builder errorblock
                                    ; buildException2 builder "wrong sum tag"

                                    ; moveBuilder builder extractblock
                                    ; datap <- buildStructGEP builder val' 2
                                    ; datap' <- buildBitCast builder datap $ ptrType $ mtype
                                                
                                    ; return datap'
                                    }            



-- stack
createStack :: LLVMBuilder -> LLVMType {- = ty -} -> LLVMValue {- = capacity -} -> IO LLVMValue {- :: (stack ty) -}
createStack builder ty capacity = do {
  ; let fctname = "createStack_" ++ show ty
  ; let fctty = fctType [int32Type] $ stackType ty
  ; let codegen = \ builder [sz] -> do { res <- createStack' builder ty sz
                                       ; return $ Just res
                                       }
  ; res <- cachedApplication builder fctname fctty codegen [capacity]
  ; return res    
}

createStack' :: LLVMBuilder -> LLVMType {- = ty -} -> LLVMValue {- = capacity -} -> IO LLVMValue {- :: (stack ty) -}
createStack' builder ty capacity | isaInt capacity = do {
                                                     -- compute the size of the array + allocate it + initialize it
                                                     ; nullp <- constNull $ ptrType $ arrayType 0 ty
                                                     ; datasz <- buildGEP builder nullp [(integer2LLVMInteger 0 32), capacity]
                                                     ; sz' <- buildPtrToInt builder datasz int64Type
                                                     ; sz <- buildIntCast builder sz' int32Type  False

                                                     ; datap <- buildAlloc2 builder sz $ arrayType 0 ty
                                                                
                                                     ; buildCounterLoop builder (integer2LLVMInteger 0 32) capacity (\ builder val -> do {
                                                                                                                                      ; ptr <- buildGEP builder datap [(integer2LLVMInteger 0 32), val]
                                                                                                                                      ; initData builder ptr
                                                                                                                                      }
                                                                                                                    )

                                                     -- allocate the structure
                                                     ; stackp <- buildAlloc builder $ stackDType ty
                                                                 
                                                     -- initialize all the fields
                                                     ; counterp <- buildStructGEP builder stackp 0
                                                     ; buildStore builder (integer2LLVMInteger 1 32) counterp
                                                     ; capacityp <- buildStructGEP builder stackp 1
                                                     ; buildStore builder capacity capacityp
                                                     ; curindexp <- buildStructGEP builder stackp 2
                                                     ; buildStore builder (integer2LLVMInteger 0 32) curindexp
                                                     ; datapp <- buildStructGEP builder stackp 3
                                                     ; buildStore builder datap datapp
                                                                  
                                                     --; buildPrintf builder ("createStack :: " ++ show ty ++ ", of capacity %d, memory size: %d , datapp: %p, datap: %p, stackp: %p :: " ++ show (stackType ty) ++ "\n") [capacity, sz, datapp, datap, stackp]
                                                                  
                                                     -- return the (properly casted) value
                                                     ; return $ typeCast stackp $ stackType ty
                                                              
                                                     }
                                 | otherwise = error $ "createStack: not a size, " ++ show capacity

stackSize :: LLVMBuilder -> LLVMValue -> IO LLVMValue
stackSize builder stack = do {
  ; let fctname = "stackSize_" ++ show (typeOf stack)
  ; let fctty = fctType [typeOf stack] int32Type
  ; let codegen = \ builder [stack] -> do { res <- stackSize' builder stack
                                         ; return $ Just res
                                         }
  ; res <- cachedApplication builder fctname fctty codegen [stack]
  ; return res    
}

stackSize' :: LLVMBuilder -> LLVMValue -> IO LLVMValue
stackSize' builder stack = do {
                           ; let TManaged (TStack ty) = rollUp $ typeOf stack
                           ; let stack' = typeCast stack $ ptrType $ stackDType ty
                           ; sizep <- buildStructGEP builder stack' 2
                           ; size <- buildLoad builder sizep
                           ; return size
                           }

stackCapacity :: LLVMBuilder -> LLVMValue -> IO LLVMValue
stackCapacity builder stack = do {
                              ; let fctname = "stackCapacity_" ++ show (typeOf stack)
                              ; let fctty = fctType [typeOf stack] int32Type
                              ; let codegen = \ builder [stack] -> do { res <- stackCapacity' builder stack
                                                                      ; return $ Just res
                                                                      }
                              ; res <- cachedApplication builder fctname fctty codegen [stack]
                              ; return res    
                              }

stackCapacity' :: LLVMBuilder -> LLVMValue -> IO LLVMValue
stackCapacity' builder stack = do {
                               ; let TManaged (TStack ty) = rollUp $ typeOf stack
                               ; let stack' = typeCast stack $ ptrType $ stackDType ty
                               ; capacityp <- buildStructGEP builder stack' 1
                               ; capacity <- buildLoad builder capacityp
                               ; return capacity
                               }

stackLookup :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> LLVMValue {- index -} -> IO LLVMValue {- ty -}
stackLookup builder stack index = do {
                                  ; let TManaged (TStack ty) = rollUp $ typeOf stack
                                  ; let fctname = "stackLookup_" ++ show (typeOf stack)
                                  ; let fctty = fctType [typeOf stack, int32Type] $ ty
                                  ; let codegen = \ builder [stack, index] -> do { res <- stackLookup' builder stack index
                                                                                 ; return $ Just res
                                                                                 }
                                  ; res <- cachedApplication builder fctname fctty codegen [stack, index]
                                  ; return res    
                                  }

stackLookup' :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> LLVMValue {- index -} -> IO LLVMValue {- ty -}
stackLookup' builder stack index = do {
                                   ; let TManaged (TStack ty) = rollUp $ typeOf stack
                                   ; let stack' = typeCast stack $ ptrType $ stackDType ty
                                   ; datapp <- buildStructGEP builder stack' 3
                                   ; datap <- buildLoad builder datapp
                                   ; mdatap <- buildGEP builder datap [(integer2LLVMInteger 0 32), index]
                                   ; mdata <- buildLoad builder mdatap
                                   ; return mdata
                                   }

stackMutate :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> LLVMValue {- index -} -> LLVMValue {- :: ty -} -> IO ()
stackMutate builder stack index val = do {
                                      ; let TManaged (TStack ty) = rollUp $ typeOf stack
                                      ; let fctname = "stackMutate_" ++ show (typeOf stack)
                                      ; let fctty = fctType [typeOf stack, int32Type, ty] voidType
                                      ; let codegen = \ builder [stack, index, val] -> do { _ <- stackMutate' builder stack index val
                                                                                          ; return Nothing
                                                                                          }
                                      ; _ <- cachedApplication builder fctname fctty codegen [stack, index, val]
                                      ; return ()

                                      }

stackMutate' :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> LLVMValue {- index -} -> LLVMValue {- :: ty -} -> IO ()
stackMutate' builder stack index val = do {
                                       ; let TManaged (TStack ty) = rollUp $ typeOf stack
                                       ; let stack' = typeCast stack $ ptrType $ stackDType ty
                                       ; datapp <- buildStructGEP builder stack' 3
                                       ; datap <- buildLoad builder datapp
                                       ; mdatap <- buildGEP builder datap [(integer2LLVMInteger 0 32), index]
                                       ; buildStore builder val mdatap
                                       }


-- we might want to put these codegen in functions ...
-- (as for incRef / decRef)
stackPop :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> IO LLVMValue
stackPop builder stack = do {
                                      ; let TManaged (TStack ty) = rollUp $ typeOf stack
                                      ; let fctname = "stackPop_" ++ show (typeOf stack)
                                      ; let fctty = fctType [typeOf stack] ty
                                      ; let codegen = \ builder [stack] -> do { res <- stackPop' builder stack
                                                                              ; return $ Just res
                                                                              }
                                      ; res <- cachedApplication builder fctname fctty codegen [stack]
                                      ; return res

                                      }
        
stackPop' :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> IO LLVMValue {- ty -}
stackPop' builder stack = do {
                                  ; let TManaged (TStack ty) = rollUp $ typeOf stack
                                  ; let stack' = typeCast stack $ ptrType $ stackDType ty
                                  ; curindexp <- buildStructGEP builder stack' 2
                                  ; curindex <- buildLoad builder curindexp
                                  ; readindex <- buildSub builder curindex (integer2LLVMInteger 1 32)
                                  ; datapp <- buildStructGEP builder stack' 3
                                  ; datap <- buildLoad builder datapp

                                  -- we should look at the size and provide exception ... TODO
                                  ; resp <- buildGEP builder datap [(integer2LLVMInteger 0 32), readindex]
                                  ; res <- buildLoad builder resp

                                  ; buildStore builder readindex curindexp

                                  ; return res

                                  }

stackPush :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> LLVMValue -> IO ()
stackPush builder stack val = do {
                                      ; let TManaged (TStack ty) = rollUp $ typeOf stack
                                      ; let fctname = "stackPush_" ++ show (typeOf stack)
                                      ; let fctty = fctType [typeOf stack, ty] voidType
                                      ; let codegen = \ builder [stack, val] -> do { _ <- stackPush' builder stack val
                                                                                   ; return Nothing
                                                                                   }
                                      ; _ <- cachedApplication builder fctname fctty codegen [stack, val]
                                      ; return ()
                              }

stackPush' :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> LLVMValue {- :: ty -} -> IO ()
stackPush' builder stack val = do {
                                       ; let TManaged (TStack ty) = rollUp $ typeOf stack
                                       ; stack' <- buildBitCast builder stack $ ptrType $ stackDType ty

                                       --; buildPrintf builder ("start, stackp: %p :: " ++ show (typeOf stack) ++ "\n") [stack']

                                       ; capacityp <- buildStructGEP builder stack' 1
                                       ; capacity <- buildLoad builder capacityp

                                       --; buildPrintf builder "capacity: %d\n" [capacity]

                                       ; curindexp <- buildStructGEP builder stack' 2
                                       ; curindex <- buildLoad builder curindexp

                                       --; buildPrintf builder "curindex: %d\n" [curindex]

                                       ; datapp <- buildStructGEP builder stack' 3
                                       ; datap <- buildLoad builder datapp

                                       --; buildPrintf builder "datapp: %p, datap: %p\n" [datapp, datap]

                                       -- we need to verify that the stack is not full
                                       -- if it is, we build a larger data block, copy the other, update the capacity
                                       -- and finally proceed with the insertion

                                       ; insertionb <- createBlock builder "insertion"
                                       ; expandb <- createBlock builder "expand"

                                       ; testres <- buildICmp builder IUGE curindex capacity
                                       ; buildCondBr builder testres expandb insertionb

                                       ; origb <- getParentBlock builder

                                       -- build the expansion code
                                       ; moveBuilder builder expandb

                                       --; buildPrintf builder "expantion\n" []

                                       -- create the new data block (new size = 10 + previous size)
                                       ; nullp <- constNull $ ptrType $ arrayType 0 ty
                                       ; olddatasz <- buildGEP builder nullp [(integer2LLVMInteger 0 32), capacity]
                                       ; oldsz' <- buildPtrToInt builder olddatasz int64Type
                                       ; oldsz <- buildIntCast builder oldsz' int32Type False

                                       ; newcapacity <- buildAdd builder capacity (integer2LLVMInteger 10 32)
                                       ; newdatasz <- buildGEP builder nullp [(integer2LLVMInteger 0 32), newcapacity]
                                       ; newsz' <- buildPtrToInt builder newdatasz int64Type
                                       ; newsz <- buildIntCast builder newsz' int32Type False

                                       --; buildPrintf builder ("extand stack :: " ++ show ty ++ ",  (capacity %d, memory size: %d) -->  (capacity %d, memory size: %d)\n") [capacity, oldsz, newcapacity, newsz]

                                       ; newdatap <- buildAlloc2 builder newsz $ arrayType 0 ty

                                       -- copy the olddata in the new one
                                       ; _ <- buildMemcpy2 builder newdatap datap oldsz

                                       -- we initialize the remaining slots
                                       ; buildCounterLoop builder curindex newcapacity (\ builder val -> do {
                                                                                           ; ptr <- buildGEP builder newdatap [(integer2LLVMInteger 0 32), val]
                                                                                           ; initData builder ptr
                                                                                           }
                                                                                       )

                                       -- we update the stack datastructure and free old data
                                       ; buildStore builder newcapacity capacityp
                                       ; buildStore builder newdatap datapp
                                       ; buildFree builder datap

                                       -- jump to the normal insertion
                                       ; buildBr builder insertionb

                                       ; deriveb <- getParentBlock builder

                                       -- the insertion block
                                       ; moveBuilder builder insertionb

                                       -- we grab the good block data pointer here
                                       ; gdatap <- buildPhi builder $ ptrType $ arrayType 0 ty
                                       ; addIncoming gdatap [(datap, origb), (newdatap, deriveb)]

                                       --; buildPrintf builder "copy, gatal: %p\n" [gdatap]

                                       -- we copy the data in the proper place
                                       ; slotp <- buildGEP builder gdatap [(integer2LLVMInteger 0 32), curindex]

                                       --; buildPrintf builder "slotp: %p\n" [slotp]

                                       ; buildStore builder val slotp

                                       --; buildPrintf builder "update index\n" []

                                       -- we update the index
                                       ; newindex <- buildAdd builder curindex (integer2LLVMInteger 1 32)
                                       ; buildStore builder newindex curindexp

                                       -- we return
                                       ; return ()

                                       }

stackCopy :: LLVMBuilder -> LLVMValue {- :: stack ty -} -> IO LLVMValue
stackCopy builder stack = do {
  ; let TManaged (TStack ty) = rollUp $ typeOf stack
  ; let fctname = "stackCopy_" ++ show (typeOf stack)
  ; let fctty = fctType [typeOf stack] $ typeOf stack
  ; let codegen = \ builder [stack] -> do { res <- stackCopy' builder stack
                                          ; return $ Just res
                                          }
  ; res <- cachedApplication builder fctname fctty codegen [stack]
  ; return res    
}

stackCopy':: LLVMBuilder -> LLVMValue {- :: stack ty -} -> IO LLVMValue
stackCopy' builder stack = do {
                           ; let TManaged (TStack ty) = rollUp $ typeOf stack
                           ; stack' <- buildBitCast builder stack $ ptrType $ stackDType ty
                                       
                           --; buildPrintf builder ("start, stackp: %p :: " ++ show (typeOf stack) ++ "\n") [stack']
                                       
                           ; capacityp <- buildStructGEP builder stack' 1
                           ; capacity <- buildLoad builder capacityp
                                         
                           --; buildPrintf builder "capacity: %d\n" [capacity]
                                         
                           ; curindexp <- buildStructGEP builder stack' 2
                           ; curindex <- buildLoad builder curindexp
                                         
                           --; buildPrintf builder "curindex: %d\n" [curindex]
                                         
                           ; datapp <- buildStructGEP builder stack' 3
                           ; datap <- buildLoad builder datapp
                                      
                           -- the new stack
                           ; newstack <- createStack builder ty capacity
                           ; newstack' <- buildBitCast builder newstack $ ptrType $ stackDType ty
                                          
                           ; newdatapp <- buildStructGEP builder newstack' 3
                           ; newdatap <- buildLoad builder newdatapp
                                         
                           -- the copy loop
                           ; buildCounterLoop builder
                                                  (integer2LLVMInteger 0 32)
                                                  curindex
                                                  (\ builder val -> do {
                                                                    ; mdatap <- buildGEP builder datap [integer2LLVMInteger 0 32, val]
                                                                    ; mutateRefFirstLevel builder mdatap True
                                                                    ; mdata <- buildLoad builder mdatap
                                                                    ; mnewdatap <- buildGEP builder newdatap [integer2LLVMInteger 0 32, val]
                                                                    ; buildStore builder mdata mnewdatap
                                                                    }
                                                  )
                           
                           -- update the index
                           ; newcurindexp <- buildStructGEP builder newstack' 2
                           ; buildStore builder curindex newcurindexp
                                        
                           ; return newstack
                           }
    


-- finalizer function
createFinalizer :: LLVMBuilder -> LLVMValue {- :: ty -} -> LLVMValue {- :: void (ty)* -} -> IO LLVMValue {- :: finalizer ty -}
createFinalizer builder value finalizer = do {
  ; let fctname = "createFinalizer_" ++ show (typeOf value)
  ; let fctty = fctType [typeOf value, ptrType $ fctType [typeOf value] voidType] $ finalizerType $ typeOf value
  ; let codegen = \ builder [value, finalizer] -> do { res <- createFinalizer' builder value finalizer
                                                    ; return $ Just res
                                                    }
  ; res <- cachedApplication builder fctname fctty codegen [value, finalizer]
  ; return res    
  }

createFinalizer' :: LLVMBuilder -> LLVMValue {- :: ty -} -> LLVMValue {- :: void (ty)* -} -> IO LLVMValue {- :: finalizer ty -}
createFinalizer' builder value finalizer = do {
                                           ; let ty' = finalizerDType $ typeOf value
                                           ; ptr <- buildAlloc builder ty'

                                           ; counterp <- buildStructGEP builder ptr 0
                                           ; _ <- buildStore builder (integer2LLVMInteger 1 32) counterp


                                           ; datap <- buildStructGEP builder ptr 1
                                           ; buildStore builder value datap

                                           ; fctp <- buildStructGEP builder ptr 2
                                           ; buildStore builder finalizer fctp

                                           ; return $ LLVMValue (valOf ptr) $ finalizerType $ typeOf value

                                           }

finalizerGetData :: LLVMBuilder -> LLVMValue {- :: finalizer ty -} -> IO LLVMValue {- ty -}
finalizerGetData builder val = do {
                               ; let TManaged (TFinalizer ty) = rollUp $ typeOf val
                               ; let val' = typeCast val $ ptrType $ finalizerDType ty

                               ; mdatap <- buildStructGEP builder val' 1
                               ; mdata <- buildLoad builder mdatap

                               ; return mdata

                               }

constArray :: [LLVMValue] -> IO LLVMValue
constArray vals = do {
                  ; ty <- toLLVMType $ typeOf $ head vals
                  ; res <- withArrayLen (map valOf vals) $ \ len ptr -> return $ LLVM.constArray ty ptr (fromIntegral len)
                  ; return $ LLVMValue res $ arrayType (fromIntegral $ length vals) $ typeOf $ head vals
                  }

-- closure functions
createClosure :: LLVMBuilder -> [LLVMValue] {- env values -} -> [LLVMType] {- argsty -} -> LLVMType {- retty -} -> LLVMValue {- the implementation function -} -> IO LLVMValue
createClosure builder envvals argtys retty fct = do {
                                                 -- grab the type of the envvals
                                                 ; let envtys = map typeOf envvals

                                                 -- we allocate the space we need
                                                 ; let ty = closureDRealType envtys argtys retty
                                                            
                                                 ; nullp <- constNull $ ptrType $ ty
                                                 ; datasz <- buildGEP builder nullp [(integer2LLVMInteger 1 32)]
                                                             
                                                 ; sz' <- buildPtrToInt builder datasz int64Type
                                                 ; sz' <- buildIntCast builder sz' int32Type False
                                                          
                                                 ; ptr <- buildAlloc2 builder sz' $ ty
                                                  
                                                 -- we fill all the fields
                                                 ; counterp <- buildStructGEP builder ptr 0
                                                 ; buildStore builder (integer2LLVMInteger 1 32) counterp

                                                 ; destroyfctp <- buildStructGEP builder ptr 1
                                                 ; destroyfct <- mkClosureDestroyFunction builder envtys argtys retty
                                                 ; buildStore builder destroyfct destroyfctp

                                                 ; applyfctp <- buildStructGEP builder ptr 2
                                                 ; applyfct <- mkClosureApplyFunction builder envtys argtys retty
                                                 ; buildStore builder applyfct applyfctp

                                                 ; computefctp <- buildStructGEP builder ptr 3
                                                 ; computefct <- mkClosureComputationFunction builder envtys argtys retty
                                                 ; buildStore builder computefct computefctp

                                                 ; envp <- buildStructGEP builder ptr 4
                                                 ; env <- createGCed builder (structType envtys)
                                                 ; buildStore builder env envp

                                                 ; envp <- getGCedData builder env

                                                 ; _ <- mapM ( \ (i, val) -> do {
                                                                             ; valp <- buildStructGEP builder envp i
                                                                             ; buildStore builder val valp
                                                                             }
                                                             ) $ zip [0..] envvals

                                                 ; triggerp <- buildStructGEP builder ptr 5
                                                 ; buildStore builder (integer2LLVMInteger (fromIntegral $ length argtys) 32) triggerp

                                                 ; argsp <- buildStructGEP builder ptr 6
                                                 ; initData builder argsp

                                                 ; fctp <- buildStructGEP builder ptr 7
                                                 ; buildStore builder fct fctp

                                                 ; res <- buildBitCast builder ptr $ closureType $ argtys ++ [retty]

                                                 ; return res

                                                }

mkClosureDestroyFunction :: LLVMBuilder -> [LLVMType] -> [LLVMType] -> LLVMType -> IO LLVMValue
mkClosureDestroyFunction builder envtys argtys retty = do {
                                                       ; mod <- getParentModule builder
                                                       ; cachedFunction mod ("closureDestroy" ++ intercalate "_" [show envtys, show argtys, show retty]) (fctType [ptrType $ int8Type] voidType) mkClosureDestroyFunction'
                                                       }
    where 
      mkClosureDestroyFunction' :: LLVMBuilder -> LLVMValue -> IO (Maybe LLVMValue)
      mkClosureDestroyFunction' builder fct = do {
                                              ; ptr <- getParam fct 0

                                              ; ptr' <- buildBitCast builder ptr $ ptrType $ closureDRealType envtys argtys retty

                                              -- decref the env
                                              ; envp <- buildStructGEP builder ptr' 4
                                              ; env <- buildLoad builder envp
                                              ; decRef builder env

                                              -- not sure it can be done dynamically ...
                                              ; argsp <- buildStructGEP builder ptr' 6

                                              ; _ <- mapM (\ i -> do {
                                                                  ; valp <- buildStructGEP builder argsp i
                                                                  ; mutateRefFirstLevel builder valp False
                                                                  }
                                                          ) [0..(length argtys - 1)]

                                              ; return Nothing
                                                
                                              }

mkClosureApplyFunction :: LLVMBuilder -> [LLVMType] -> [LLVMType] -> LLVMType -> IO LLVMValue
mkClosureApplyFunction builder envtys argtys retty = do {
                                                       ; mod <- getParentModule builder
                                                       ; cachedFunction mod ("closureApply" ++ intercalate "_" [show envtys, show argtys, show retty]) (fctVarargType [ptrType $ int8Type, int8Type] voidType) mkClosureApplyFunction'
                                                       }
    where 
      mkClosureApplyFunction' :: LLVMBuilder -> LLVMValue -> IO (Maybe LLVMValue)
      mkClosureApplyFunction' builder fct = do {
                                            ; ptr <- getParam fct 0
                                                     
                                            ; nbapply <- getParam fct 1

                                            ; (valist, vaarg) <- getVarArgs builder fct

                                            ; ptr' <- buildBitCast builder ptr $ ptrType $ closureDRealType envtys argtys retty                                                      

                                            ; let nbargs = length argtys
                                                    
                                            -- we create staically all the blocks (and the end block)
                                            ; endblock <- createBlock builder "apply end"
                                            ; casesblock <- mapM (\ i -> createBlock builder ("get & set arg " ++ show i)) [0..(nbargs-1)]
       
                                            -- we set a local mutable var in order to keep the number of arg to apply
                                            ; nbapplyp <- buildAlloca builder int8Type
                                            ; buildStore builder nbapply nbapplyp

                                            -- the first arg to set
                                            ; triggerp <- buildStructGEP builder ptr' 5
                                            ; trigger <- buildLoad builder triggerp
                                            ; firstarg <- buildSub builder (integer2LLVMInteger (fromIntegral nbargs) 32) trigger 
                                            ; nbapply' <- buildIntCast builder nbapply int32Type False
                                            ; newtrigger <- buildSub builder trigger nbapply'
                                            ; buildStore builder newtrigger triggerp 

                                            ; argsp <- buildStructGEP builder ptr' 6

                                            -- build the select
                                            ; buildSwitch builder firstarg (zip (map (\ x -> integer2LLVMInteger (fromIntegral x) 32) [0..(nbargs-1)]) casesblock) endblock

                                            -- build the code blocks
                                            ; _ <- mapM (\ i -> do {
                                                                -- go to the proper block
                                                                ; moveBuilder builder $ casesblock!!i
                                                                -- load the value and set it in the proper 
                                                                ; valp <- buildStructGEP builder argsp (fromIntegral i)
                                                                ; val <- buildGetVarArg builder vaarg $ argtys!!i
                                                                ; buildStore builder val valp

                                                                -- now we decrement the number of apply and test if we are done
                                                                -- if yes go to the end, else to the next block 
                                                                ; if (i /= (nbargs-1)) then do {
                                                                                            ; nbapply <- buildLoad builder nbapplyp
                                                                                            ; nbapply <- buildSub builder nbapply (integer2LLVMInteger 1 8)
                                                                                            ; buildStore builder nbapply nbapplyp
                                                                                            ; cond <- buildICmp builder IEQ nbapply (integer2LLVMInteger 0 8)                                                                ; 
                                                                                            ; buildCondBr builder cond endblock $ casesblock!!(i+1)
                                                                                            }
                                                                  else do {
                                                                         ; buildBr builder endblock
                                                                       }
                                                                }
                                                        ) [0..(nbargs-1)]

                                            -- the end block
                                            ; moveBuilder builder endblock

                                            ; endVarArgs builder valist

                                            ; return Nothing
                                                
                                            }


mkClosureComputationFunction :: LLVMBuilder -> [LLVMType] -> [LLVMType] -> LLVMType -> IO LLVMValue
mkClosureComputationFunction builder envtys argtys retty = do {
                                                       ; mod <- getParentModule builder
                                                       ; cachedFunction mod ("closureCompute" ++ intercalate "_" [show envtys, show argtys, show retty]) (fctType [ptrType $ int8Type] $ retty) mkClosureComputationFunction'
                                                       }
    where 
      mkClosureComputationFunction' :: LLVMBuilder -> LLVMValue -> IO (Maybe LLVMValue)
      mkClosureComputationFunction' builder fct = do {
                                                  ; ptr <- getParam fct 0
                                                           
                                                  ; ptr' <- buildBitCast builder ptr $ ptrType $ closureDRealType envtys argtys retty
                                                            
                                                  -- decref the env
                                                  ; envp <- buildStructGEP builder ptr' 4
                                                  ; env <- buildLoad builder envp
                                                  ; env <- getGCedData builder env

                                                  ; args <- buildStructGEP builder ptr' 6

                                                  ; bodyfctp <- buildStructGEP builder ptr' 7
                                                  ; bodyfct <- buildLoad builder bodyfctp

                                                  ; res <- buildCall builder bodyfct [env, args]

                                                  ; return $ Just res

                                                  }

destroyClosure :: LLVMBuilder -> LLVMValue {- :: TClosure _ -} -> IO ()
destroyClosure builder closure = do {
                                 ; let TManaged (TClosure tys) = rollUp $ typeOf closure

                                 ; let ptr' = typeCast closure $ ptrType $ closureDType tys
                                              
                                 -- grab the destroy function and call it on the closure
                                 ; destroyfctp <- buildStructGEP builder ptr' 1
                                 ; destroyfct <- buildLoad builder destroyfctp

                                 ; ptr <- buildBitCast builder closure $ ptrType $ int8Type

                                 ; _ <- buildCall builder destroyfct [ptr]

                                 ; return ()
                                 }

applyClosure :: LLVMBuilder -> LLVMValue -> [LLVMValue] -> IO LLVMValue
applyClosure builder closure args = do {
                                 ; let TManaged (TClosure tys) = rollUp $ typeOf closure

                                 ; let ptr' = typeCast closure $ ptrType $ closureDType tys
                                              
                                 -- grab the apply function and call it on the closure
                                 ; applyfctp <- buildStructGEP builder ptr' 2
                                 ; applyfct <- buildLoad builder applyfctp

                                 ; ptr <- buildBitCast builder closure $ ptrType $ int8Type

                                 ; _ <- buildCall builder applyfct $ [ptr, (integer2LLVMInteger (fromIntegral $ length args) 8)] ++ args

                                 ; return $ LLVMValue (valOf closure) $ closureType $ drop (length args) tys
                                 }

computeClosure :: LLVMBuilder -> LLVMValue -> IO LLVMValue
computeClosure builder closure = do {
                                 ; let TManaged (TClosure [ty]) = rollUp $ typeOf closure
                                                                  
                                 ; let ptr' = typeCast closure $ ptrType $ closureDType [ty]
                                              
                                 -- grab the compute function and call it on the closure
                                 ; computefctp <- buildStructGEP builder ptr' 3
                                 ; computefct <- buildLoad builder computefctp
                                                 
                                 ; ptr <- buildBitCast builder closure $ ptrType $ int8Type
                                          
                                 ; res <- buildCall builder computefct [ptr]
                                          
                                 ; return res
                                 }
    
-- helper function

constString :: String -> IO LLVMValue
constString name = do {
                   ; mname <- newCString name
                   ; let res = LLVM.constString mname (fromIntegral $ length name) (fromIntegral 0)
                   ; resty <- LLVM.typeOf res
                   ; ty <- fromLLVMType resty
                   ; return $ LLVMValue res ty
                   }


-- runtime functions

-- error/exception

-- really strange ....
foreign import ccall "&llvmexception"
        imported_llvmexception :: FunPtr (CString -> IO CInt)

foreign export ccall llvmexception :: CString -> IO CInt

llvmexception :: CString -> IO CInt
llvmexception err = do {
                    ; s <- peekCAString err
                    ; error $ "llvmexception: " ++ s
                    }


buildException :: LLVMBuilder -> String -> LLVMType -> IO LLVMValue
buildException builder s ty = do {
                              ; ty' <- toLLVMType ty
                              ; mod <- getParentModule builder
                              ; f <- getFunction mod "llvmexception"
                              ; s' <- constString s
                              ; msg <- buildInternAlloc builder $ typeOf s'
                              ; buildStore builder s' msg
                              ; fct <- case f of
                                         Just f -> return f
                                         Nothing -> do {
                                                    ; f <- addFunction2 mod "llvmexception" $ fctType [ptrType int8Type] voidType
                                                    ; return f
                                                    }
                              ; msg' <- buildBitCast builder msg $ ptrType int8Type
                              ; _ <- buildCall builder fct [msg']
                              ; buildInternFree builder msg
                              ; res <- getUndef ty
                              ; return res
                              }

-- this version does not return a value, but push an unreachable terminator
buildException2 :: LLVMBuilder -> String -> IO ()
buildException2 builder s = do {
                            ; mod <- getParentModule builder
                            ; f <- getFunction mod "llvmexception"
                            ; s' <- constString s
                            ; msg <- buildInternAlloc builder $ typeOf s'
                            ; buildStore builder s' msg
                            ; fct <- case f of
                                       Just f -> return f
                                       Nothing -> do {
                                                  ; f <- addFunction2 mod "llvmexception" $ fctType [ptrType int8Type] voidType
                                                  ; return f
                                                  }
                            ; msg' <- buildBitCast builder msg $ ptrType int8Type
                            ; _ <- buildCall builder fct [msg']
                            ; buildInternFree builder msg
                            ; buildUnreachable builder
                            }

-- debug message

-- really strange ....
foreign import ccall "&llvmdebugmsg"
        imported_llvmdebugmsg :: FunPtr (CString -> IO CInt)

foreign export ccall llvmdebugmsg :: CString -> IO CInt

llvmdebugmsg :: CString -> IO CInt
llvmdebugmsg err = do {
                   ; s <- peekCAString err
                   ; putTraceMsg $ "\ndebugMsg: " ++ s ++ "\n"
                   ; return $ fromIntegral 0
                   }


buildDebugMsg :: LLVMBuilder -> String -> IO ()
buildDebugMsg builder s = do {
                          ; mod <- getParentModule builder
                          ; f <- getFunction2 mod "llvmdebugmsg" $ ptrType $ fctType [ptrType int8Type] voidType
                          ; s' <- constString s
                          ; msg <- buildInternAlloc builder $ typeOf s'
                          ; buildStore builder s' msg
                          ; fct <- case f of
                                     Just f -> return f
                                     Nothing -> do {
                                                ; f <- addFunction2 mod "llvmdebugmsg" $ fctType [ptrType int8Type] voidType
                                                ; return f
                                                }
                          ; msg' <- buildBitCast builder msg $ ptrType int8Type
                          ; _ <- buildCall builder fct [msg']
                          ; buildInternFree builder msg
                          ; return ()
  }

-- the printf !!!
buildPrintf :: LLVMBuilder -> String -> [LLVMValue] -> IO ()
buildPrintf builder s args = do {
                             ; mod <- getParentModule builder
                             ; f <- getFunction mod "printf"
                             ; s' <- constString s
                             ; msg <- buildAlloc builder $ typeOf s'
                             ; buildStore builder s' msg
                             ; fct <- case f of 
                                        Just f -> return $ valOf f
                                        Nothing -> do {
                                                   ; let ty = [LLVM.pointerType (LLVM.integerType (fromIntegral 8)) (fromInteger 0)]
                                                   ; fty <- liftIO $ withArrayLen ty
                                                            $ \ len ptr -> return $ LLVM.functionType LLVM.int32Type ptr (fromIntegral len) (fromInteger 1)
                                                   ; cname <- newCString "printf"
                                                   ; f <- LLVM.addFunction mod cname fty
                                                   ; _ <- free cname
                                                   ; return f
                                                   }
                             ; cname <- newCString $ ""
                             ; args' <- mapM toLLVMValue args
                             ; msg' <- buildBitCast builder msg $ ptrType int8Type
                             ; _ <- withArrayLen ((valOf msg'):args') $ \ len ptr -> LLVM.buildCall builder fct ptr (fromIntegral len) cname
                             ; _ <- free cname
                             ; buildFree builder msg
                             ; return ()
                             }

-- memory allocation registration
-- for now the infamous "unsafePerformIO hack"

memRegistry :: HashTable.HashTable Int String
{-# NOINLINE memRegistry #-}
memRegistry = unsafePerformIO $ do {
                                ; h <- HashTable.new (==) HashTable.hashInt
                                ; return h
                                }

llvmRegisterAlloc :: Ptr () -> CString -> IO CInt
llvmRegisterAlloc ptr ty = do {
                           ; let addr = fromIntegral $ ptrToIntPtr ptr
                           --; putStrLn $ "Registering " ++ show (ptr, addr)
                           ; ty' <- peekCAString ty
                           ; exists <- HashTable.lookup memRegistry addr
                           ; case exists of
                               Nothing -> return ()
                               Just _ -> error $ "Catastrophic: the register alloc address already exists, " ++ show (ptr, addr)
                           ; HashTable.insert memRegistry addr ty'
                           ; return $ fromIntegral 0
                           }

buildRegisterAlloc :: LLVMBuilder -> LLVMValue -> IO ()
buildRegisterAlloc builder ptr = do {
                                 ; mod <- getParentModule builder
                                 ; f <- getFunction mod "llvmRegisterAlloc"
                                 ; s' <- constString $ show $ typeOf ptr
                                 ; msg <- buildInternAlloc builder $ typeOf s'
                                 ; buildStore builder s' msg
                                 ; fct <- case f of
                                            Just f -> return f
                                            Nothing -> do {
                                                       ; f <- addFunction2 mod "llvmRegisterAlloc" $ fctType [ptrType int8Type, ptrType int8Type] voidType
                                                       ; return f
                                                       }
                                 ; ptr' <- buildBitCast builder ptr $ ptrType int8Type
                                 ; msg' <- buildBitCast builder msg $ ptrType int8Type
                                 ; _ <- buildCall builder fct [ptr', msg']
                                 ; buildInternFree builder msg
                                 ; return ()
                                 }


foreign export ccall llvmRegisterAlloc :: Ptr () -> CString -> IO CInt

foreign import ccall "&llvmRegisterAlloc"
        imported_llvmRegisterAlloc :: FunPtr (Ptr () -> CString -> IO CInt)

llvmRegisterFree ::  Ptr () -> IO CInt
llvmRegisterFree ptr = do {
                       ; let addr = fromIntegral $ ptrToIntPtr ptr
                       --; putStrLn $ "Unregistering " ++ show (ptr, addr)
                       ; exists <- HashTable.lookup memRegistry addr
                       ; case exists of
                           Nothing -> error "Catastrophic: the register free address not registered"
                           Just _ -> return ()
                       ; HashTable.delete memRegistry addr
                       ; return $ fromIntegral 0
                       }

foreign export ccall llvmRegisterFree :: Ptr () -> IO CInt

foreign import ccall "&llvmRegisterFree"
        imported_llvmRegisterFree :: FunPtr (Ptr () -> IO CInt)

buildRegisterFree :: LLVMBuilder -> LLVMValue -> IO ()
buildRegisterFree builder ptr = do {
                                ; mod <- getParentModule builder
                                ; f <- getFunction mod "llvmRegisterFree"
                                ; fct <- case f of
                                           Just f -> return f
                                           Nothing -> do {
                                                      ; f <- addFunction mod "llvmRegisterFree" [ptrType int8Type] voidType
                                                      ; return f
                                                      }
                                ; ptr' <- buildBitCast builder ptr $ ptrType int8Type
                                ; _ <- buildCall builder fct [ptr']
                                ; return ()
                                }

showMemUsage :: IO ()
showMemUsage = do { lst <- HashTable.toList memRegistry
                  ; when memProfiling $ do {
                                        ; putStrLn " Memory Usage: "
                                        ; _ <- mapM (\ (addr, ty) -> putStrLn $ show (intPtrToPtr $ fromIntegral addr) ++ " :: " ++ show ty) lst
                                        ; return ()
                                        }
                  ; return ()
                  }

freeGCMem :: IO ()
freeGCMem = do {
            ; lst <- HashTable.toList memRegistry
            ; when memProfiling $ do {
                                  ; res <- mapM (\ (addr, _) -> do {
                                                                ; HashTable.delete memRegistry addr
                                                                ; free $ intPtrToPtr $ fromIntegral addr
                                                                }) lst
                                  ; putStrLn $ "freeGCMem: " ++ show res
                                  }
            }


---------------------------------------------------

isTrue :: LLVMValue -> Bool
isTrue = unsafePerformIO . isTrue'
    where
        isTrue' :: LLVMValue -> IO Bool
        isTrue' val | typeOf val == boolType = do {
            ; b <- isConstant val
            ; if b then isNull val else return False
            }
