{-# LANGUAGE ExistentialQuantification, FlexibleInstances, RankNTypes, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, UndecidableInstances #-}
module VM (
  VMOpcode(..), VMData(..), VMValue(..), VMState(..), VMType(..), VMPrimitive(..),
  ObjectBlock, CodeBlock, showVMData,
  codeBlock2String, objectBlock2String,
  linkObjectBlock, vmExec,
  saveObjectBlocks, loadObjectBlocks,

  testVM,
  
  --
  
  vmTypes, buildTopLevel,
  printVMData,
  
  ) where


import Debug.Trace(trace, putTraceMsg)

import qualified Data.Array as A
import Data.Array((!))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe(fromJust)
import Data.List(intercalate)
import Control.Monad

import LLVMBinding

import Foreign.Ptr

import System.IO

-- The VM Definition

-- | Type parameter for label or address
data VMOpcode a = ACCESSVOL Int
                | ACCESSFIX Int

                | PUSH VMValue

                -- here the filter are represented as a couple of list of Int
                -- the first one represent the indices (reverse debruijn) from the fixenv (order: decresing deBruijn Index)
                -- the second one represent the indices (reverse debruijn) from the volenv (order: decresing deBruijn Index)
                | CLOSURE a [(String, VMType)] VMType ([Int], [Int])
                | RECURSION a String [(String, VMType)] VMType ([Int], [Int])
                | RETURN
                | SWAP [String] {- names -} Int {- length -}
                | POPENV Int
                | APPLY Int
                | JMPC a
                | JMP a

                  -- to be dropped in a first version
                | CONSTRUCTOR Int String
                | DESTRUCTOR [a]

                | NOP
                | DEALLOCATE [Int]
                | BREAK
                | START String
                | STOP
                | PRIMITIVE VMPrimitive
                | TOTPRIMITIVE VMPrimitive

                | DEBUGMSG String
                deriving (Eq, Ord, Show, Read)

data VMPrimitive = PIEq
                 | PISub
                 | PDAdd
                   deriving (Eq, Ord, Show, Read, Enum, Bounded)

data VMValue = VInt Int
             | VDouble Double
             | VBool Bool
               deriving (Eq, Ord, Show, Read)

data VMType = TInt
            | TDouble
            | TBool
              deriving (Eq, Ord, Show, Read)

data VMData a = CL a [VMData a] {- fixenv -} [VMData a] {- volenv -} [(String, VMType)] VMType
              | REC a String [VMData a] [(String, VMType)] VMType
              | FRAME a [VMData a] [VMData a]
              | PRIM VMPrimitive [VMData a] {- ([VMData] -> VMData) ??? -}
              | CONSTR Int String [VMData a]
              | VAL VMValue
              deriving (Eq, Ord, Show, Read)


showVMData :: (Show a) => VMData a -> String
showVMData (CL adr fenv volenv args retty) = "Closure :: " ++ show ""
showVMData (REC adr name fenv args retty) = "RecClosure :: " ++ show ""
showVMData (FRAME _ _ _) = "Frame"
showVMData (PRIM p args) = show p ++ " :: " ++ show ""
showVMData (VAL v) = show v
showVMData (CONSTR p s args) = s ++ " " ++ intercalate " " (map showVMData args)

-- We define the object code for the VM opcode
type ObjectBlock = [(Maybe String, VMOpcode String)] -- Each VMOpcode maybe labeled with a string
                   
objectBlock2String :: ObjectBlock -> String
objectBlock2String cb =
    let labels = [ length l | (Just l, _) <- cb] in
    let maxsizelabel = foldl max 0 labels in
    (intercalate "\n" $ map (\ (label, code) ->
                              (case label of
                                  Nothing -> replicate maxsizelabel ' '
                                  Just l -> replicate (maxsizelabel - length l) ' ' ++ l
                              ) ++ ": " ++ show code
                            ) cb) ++ "\n"

-- The linking function, taking the entry symbol and returning a CodeBlock
linkObjectBlock :: [ObjectBlock] -> String -> (CodeBlock, Int)
linkObjectBlock objectcode entry =
  let (symbmap, code) = concatblock [] Map.empty (Set.singleton entry) in
  (opcodesToCodeBlock $ link $ (symbmap, code), fromJust $ Map.lookup entry symbmap)
    where
      concatblock :: [VMOpcode String] -> Map.Map String Int -> Set.Set String -> (Map.Map String Int, [VMOpcode String])
      concatblock done symbolsmap missingsymbols =
          if Set.null missingsymbols then (symbolsmap, done)
          else
              -- grab the first missing symbol
              let missingsymb = head $ Set.toList missingsymbols in -- Why no Data.Set.choice in O(1)? Sigh.
              -- we grab the corresponding block with its local symbol map and missing symbol set
              let Just (block, defined, used) = definingcode missingsymb in
              -- the new set of missing symbols
              let missingsymbols' = Set.union
                                      (Set.delete missingsymb (Set.difference missingsymbols (Map.keysSet defined)))
                                      (Set.difference used (Map.keysSet symbolsmap)) in
              -- the new symbols map (shifted)
              let symbolsmap' = Map.union (Map.map ((+) $ length done) defined) symbolsmap in -- CR jfuruse: length done : O(n)
              -- we merge the block
              let done' = done ++ map snd block in
              -- we tail-call ourselves
              concatblock done' symbolsmap' missingsymbols'

      -- The final label => address resolution
      link :: (Map.Map String Int, [VMOpcode String]) -> [VMOpcode Int]
      link (smap, code) = map (fmap $ \ s -> fromJust $ Map.lookup s smap) code

      -- returns the block defining the string, together with its defined symbol and used external symbols
      definingcode :: String -> Maybe (ObjectBlock, Map.Map String Int, Set.Set String)
      definingcode symbol =
          -- we grab the blocks that defined the symbols (error if 0 or n blocks defines it)
          -- we clearly use the lazyness of Haskell in the following code
          let [block_defined_used] = filter (\ (blk, defined, used) ->
                                                 Set.member symbol $ Map.keysSet defined) symbolinfo in
          Just block_defined_used

      symbolinfo :: [(ObjectBlock,
                      Map.Map String Int, -- Defined symbols with the relative addresses from the block head
                      Set.Set String -- Used external symbols
                     )]
      symbolinfo = map (\ b ->
                        let defined = definedsymbol b in
                        let used = usedsymbol b in
                        (b, defined, Set.difference used $ Map.keysSet defined)) objectcode
          where
              definedsymbol :: ObjectBlock -> Map.Map String Int
              definedsymbol objectblk = foldl (\ acc (i, (s, _)) ->
                                               case s of
                                                   Nothing -> acc
                                                   Just s -> Map.insert s i acc
                                              ) Map.empty $ zip [0..] objectblk

              usedsymbol :: ObjectBlock -> Set.Set String
              -- just a fold with set insertion
              usedsymbol objectblk = foldl (\ acc (_, o) ->
                                            case o of
                                              CLOSURE addr _ _ _ -> Set.insert addr acc
                                              RECURSION addr _ _ _ _ -> Set.insert addr acc
                                              JMPC addr -> Set.insert addr acc
                                              JMP addr -> Set.insert addr acc
                                              DESTRUCTOR addrs -> Set.union (Set.fromList addrs) acc
                                              _ -> acc
                                           ) Set.empty objectblk

-- CodeBlock are basically used for the executable version of VM code, thus VMOpcode Int
type CodeBlock = A.Array Int (VMOpcode Int)

codeBlock2String :: CodeBlock -> String
codeBlock2String cb = (intercalate "\n" $ map show $ A.elems cb) ++ "\n"


-- N.B.: for sake of efficiency: the volenv and fixenv are in Debruijn index increasing order
data VMState = VMState { volenv :: [VMData Int],
                         fixenv :: [VMData Int],
                         stack :: [VMData Int],
                         pc :: Int
                         -- code :: CodeBlock, -- code is constant and out of the state
                       }
             deriving (Eq, Ord, Show, Read)

-- execution

-- this is completely reverse with a low-level implem
filterapply :: [VMData a] -> [VMData a] -> ([Int], [Int]) -> [VMData a]
filterapply venv fenv (ffilter, vfilter) = let ffiltered = map (\ i -> let rindex = length fenv - i - 1 in
                                                                        let val = (fenv!!rindex) in
                                                                        val
                                                                        ) $ reverse ffilter in
                                           let vfiltered = map (\ i -> let rindex = length venv - i - 1 in
                                                                        let val = (venv!!rindex) in
                                                                        val) $ reverse vfilter in
                                           vfiltered ++ ffiltered


arity :: VMPrimitive -> Int
arity PIEq = 2
arity PISub = 2
arity PDAdd = 2

primSemantics :: VMPrimitive -> [VMData a] -> VMData a
primSemantics PIEq = \ [VAL (VInt i1), VAL (VInt i2)] -> VAL $ VBool $ i1 == i2
primSemantics PISub = \ [VAL (VInt i1), VAL (VInt i2)] -> VAL $ VInt $ i1 - i2
primSemantics PDAdd = \ [VAL (VDouble d1), VAL (VDouble d2)] -> VAL $ VDouble $ d1 +d2

stckdeepness :: [VMData Int] -> Int
stckdeepness [] = 0
stckdeepness ((FRAME _ _ _):tl) = 1 + stckdeepness tl
stckdeepness ((_):tl) = stckdeepness tl

vmExec :: CodeBlock -> VMState -> VMData Int
vmExec c (VMState venv fenv stck pc) = vmExec' venv fenv stck pc
    where
      vmExec' :: [VMData Int] -> [VMData Int] -> [VMData Int] -> Int -> VMData Int
      vmExec' venv fenv stck pc =
          --trace (show pc ++ ": " ++ replicate (stckdeepness stck) '\t' ++ show (c!pc) ++ ", stack := " ++ show stck) $
          case c!pc of
            NOP -> vmExec' venv fenv stck (pc+1)

            JMP a -> vmExec' venv fenv stck a

            JMPC a ->
                case stck of
                  (VAL (VBool b)):stck' ->
                      if b then vmExec' venv fenv stck' (pc+1)
                      else vmExec' venv fenv stck' a
                  _ -> error "Catastrophic: VM has the wrong configuration for JMPC"

            ACCESSVOL i ->
                let rindex = length venv - i - 1 in
                let val = (venv!!rindex) in
                vmExec' venv fenv (val:stck) (pc+1)

            ACCESSFIX i ->
                let rindex = length fenv - i - 1 in
                let val = (fenv!!rindex) in
                vmExec' venv fenv (val:stck) (pc+1)

            PUSH d ->
                vmExec' venv fenv ((VAL d):stck) (pc+1)

            CLOSURE adr args retty filter ->
                let top = CL adr (filterapply venv fenv filter) [] args retty in
                vmExec' venv fenv (top:stck) (pc+1)

            RECURSION adr name args retty filter ->
                let top = REC adr name (filterapply venv fenv filter) args retty in
                vmExec' venv fenv (top:stck) (pc+1)

            RETURN ->
                case stck of
                  [vmdata] -> vmdata
                  val:(FRAME adr fenv venv):stck' -> vmExec' venv fenv (val:stck') adr
                  _ -> error $ "VM has the wrong configuration for RETURN: " ++ show stck

            SWAP names size ->
                let venv' = (reverse $ take size stck) ++ venv in
                vmExec' venv' fenv (drop size stck) (pc+1)

            POPENV i ->
                let venv' = drop i venv in
                vmExec' venv' fenv stck (pc+1)

            CONSTRUCTOR i n ->
                let top = CONSTR i n [] in
                vmExec' venv fenv (top:stck) (pc+1)

            DESTRUCTOR addrs ->
                case stck of
                  (CONSTR i n args):stck' -> vmExec' (args ++ venv) fenv stck' (addrs!!i)
                  _ -> error $ "VM has the wrong configuration for DESTRUCTOR "

            DEALLOCATE l ->
                vmExec' venv fenv stck (pc+1)

            PRIMITIVE p ->
                let top = PRIM p [] in
                vmExec' venv fenv (top:stck) (pc+1)

            TOTPRIMITIVE p ->
                let i = arity p in
                let top = primSemantics p $ (reverse $ take i stck) in
                let stck' = top:(drop i stck) in
                vmExec' venv fenv stck' (pc+1)

            DEBUGMSG s ->
                trace s $ vmExec' venv fenv stck (pc+1)


            APPLY i ->
                let fct = stck!!i in
                case fct of

                  CL adr fenv' applied args retty | i == length args ->
                                                      let frame = FRAME (pc+1) fenv venv in
                                                      let venv' = take i stck ++ applied in
                                                      let stck' = frame:(drop (i+1) stck) in
                                                      vmExec' venv' fenv' stck' adr

                  CL adr fenv' applied args retty | i < length args ->
                                                      let top = CL adr fenv' (take i stck ++ applied) (drop i args) retty in
                                                      let stck' = top:(drop (i+1) stck) in
                                                      vmExec' venv fenv stck' (pc+1)

                  r@(REC adr name fenv' args retty) | i < length args ->
                                                        let top = CL adr (r:fenv') (take i stck) (drop i args) retty in
                                                        let stck' = top:(drop (i+1) stck) in
                                                        vmExec' venv fenv stck' (pc+1)

                  r@(REC adr name fenv' args retty) | i == length args ->
                                                        let fenv'' = r:fenv' in
                                                        let top = FRAME (pc+1) fenv venv in
                                                        let stck' = top:(drop (i+1) stck) in
                                                        let venv' = (take i stck) in
                                                        vmExec' venv' fenv'' stck' adr

                  PRIM p args | i + length args < arity p ->
                                  let top = PRIM p (args ++ (reverse $ take i stck)) in
                                  let stck' = top:(drop (i+1) stck) in
                                  vmExec' venv fenv stck' (pc+1)

                  PRIM p args | i + length args == arity p ->
                                  let top = primSemantics p $ (args ++ (reverse $ take i stck)) in
                                  let stck' = top:(drop (i+1) stck) in
                                  vmExec' venv fenv stck' (pc+1)

                  CONSTR p s args ->
                      let top = CONSTR p s (take i stck ++ args) in
                      let stck' = top:(drop (i+1) stck) in
                      vmExec' venv fenv stck' (pc+1)

                  _ -> error "VM has wrong configuration for APPLY"


            o  -> error $ "opcode not yet supported: " ++ show o


instance Functor VMData where
    -- fmap :: (a -> b) -> VMData a -> VMData b
    fmap f d = case d of
        CL a ds1 ds2 args ty -> CL (f a) (map (fmap f) ds1) (map (fmap f) ds2) args ty
        REC a name ds args ty -> REC (f a) name (map (fmap f) ds) args ty
        FRAME a ds1 ds2 -> FRAME (f a) (map (fmap f) ds1) (map (fmap f) ds2)
        PRIM p ds -> PRIM p (map (fmap f) ds)
        CONSTR n name ds -> CONSTR n name (map (fmap f) ds)
        VAL v -> VAL v

instance Functor VMOpcode where
    -- fmap :: (a -> b) -> VMOpcode a -> VMOpcode b
    fmap f v = case v of
        PUSH vmVal -> PUSH vmVal
        CLOSURE a args ty ls -> CLOSURE (f a) args ty ls
        RECURSION a name args ty ls -> RECURSION (f a) name args ty ls
        JMPC a -> JMPC $ f a
        JMP a -> JMP $ f a
        DESTRUCTOR as -> DESTRUCTOR $ map f as

        ACCESSVOL n -> ACCESSVOL n
        ACCESSFIX n -> ACCESSFIX n
        RETURN -> RETURN
        SWAP ls sz -> SWAP ls sz
        POPENV n -> POPENV n
        APPLY n -> APPLY n
        CONSTRUCTOR n name -> CONSTRUCTOR n name
        NOP -> NOP
        DEALLOCATE ns -> DEALLOCATE ns
        BREAK -> BREAK
        START name -> START name
        STOP -> STOP
        PRIMITIVE p -> PRIMITIVE p
        TOTPRIMITIVE p -> TOTPRIMITIVE p
        DEBUGMSG s -> DEBUGMSG s

opcodesToCodeBlock :: [VMOpcode Int] -> CodeBlock
opcodesToCodeBlock vmops = A.listArray (0,length vmops -1) vmops

testVM :: ([ObjectBlock], String) -> VMData Int
testVM code =
    let (obj, entry) = code in
    let (code, _) = linkObjectBlock obj entry in
    let volenv = [] in
    let fixenv = [] in
    let stack = [] in
    let pc = 0 in
    let st = VMState volenv fixenv stack pc in
    vmExec code st

saveObjectBlocks :: [ObjectBlock] -> String -> IO ()
saveObjectBlocks blocks fname = do {
  ; h <- openFile fname WriteMode
  ; hPutStr h $ show blocks
  ; hClose h
  }
                                
loadObjectBlocks :: String -> IO [ObjectBlock]
loadObjectBlocks fname = do {
  ; h <- openFile fname ReadMode
  ; s <- hGetContents h
  ; res <- return $ read s
  ; return res
  }

-- LLVM interpreter

-- definition of types for VM
-- they are mutally recursive, and so to avoid loop in LLVMType building we use recursive types of LLVMType

vmTypesDef :: [(String, LLVMType)]
vmTypesDef = [("vmDataType", sumType [varType "vmDataVALType", varType "vmDataPRIMType", varType "vmDataFRAMEType", varType "vmDataRECType", varType "vmDataCLType", varType "vmDataCONSTRType"]),
              ("vmDataVALType", sumType [int32Type, doubleType, boolType]),
              ("vmDataPRIMType", structType [int8Type, varType "vmVolenvType"]),
              ("vmDataFRAMEType", structType [int32Type, varType "vmFixenvType", varType "vmVolenvType"]),
              ("vmDataRECType", structType [int32Type, varType "vmFixenvType", int8Type]),
              ("vmDataCLType", structType [int32Type, varType "vmFixenvType", varType "vmVolenvType", int8Type]),
              ("vmDataCONSTRType", structType [int8Type, varType "vmVolenvType"]),
              ("vmStackType", stackType $ varType "vmDataType"),
              ("vmVolenvType", stackType $ varType "vmDataType"),
              ("vmFixenvType", dynArrayType $ varType "vmDataType")
             ]

vmTypes :: [(String, LLVMType)]
vmTypes = recDef vmTypesDef

-- the vm state container

vmFixenvType :: LLVMType
vmFixenvType = fromJust $ lookup "vmFixenvType" vmTypes

vmVolenvType :: LLVMType
vmVolenvType = fromJust $ lookup "vmVolenvType" vmTypes

vmStackType :: LLVMType
vmStackType = fromJust $ lookup "vmStackType" vmTypes

-- the vmData

vmDataCLType :: LLVMType
vmDataCLType = fromJust $ lookup "vmDataCLType" vmTypes

vmDataRECType :: LLVMType
vmDataRECType = fromJust $ lookup "vmDataRECType" vmTypes

vmDataFRAMEType :: LLVMType
vmDataFRAMEType = fromJust $ lookup "vmDataFRAMEType" vmTypes

vmDataPRIMType :: LLVMType
vmDataPRIMType = fromJust $ lookup "vmDataPRIMType" vmTypes

-- dummy type for Cortex Values ...
vmDataVALType :: LLVMType
vmDataVALType = fromJust $ lookup "vmDataVALType" vmTypes

vmDataType :: LLVMType
vmDataType = fromJust $ lookup "vmDataType" vmTypes

-- data arity + indexes

dataTypeSetArity :: Int
dataTypeSetArity = 5

vmDataVALTypeIndex :: Int
vmDataVALTypeIndex = 0

vmDataPRIMTypeIndex :: Int
vmDataPRIMTypeIndex = 1

vmDataFRAMETypeIndex :: Int
vmDataFRAMETypeIndex = 2

vmDataRECTypeIndex :: Int
vmDataRECTypeIndex = 3

vmDataCLTypeIndex :: Int
vmDataCLTypeIndex = 4

vmDataCONSTRTypeIndex :: Int
vmDataCONSTRTypeIndex = 5

vmDataIntIndex :: Int
vmDataIntIndex = 0

vmDataDoubleIndex :: Int
vmDataDoubleIndex = 1

vmDataBoolIndex :: Int
vmDataBoolIndex = 2

-- helper functions

frameFromVMData :: LLVMBuilder -> LLVMValue {- :: vmDataType -} -> IO LLVMValue {- vmDataFRAMEType* -}
frameFromVMData builder vmdata = extractFromSum builder vmdata vmDataFRAMETypeIndex

valFromVMData :: LLVMBuilder -> LLVMValue {- :: vmDataType -} -> IO LLVMValue {- vmDataVALType* -}
valFromVMData builder vmdata = extractFromSum builder vmdata vmDataVALTypeIndex

boolFromVMDataVAL :: LLVMBuilder -> LLVMValue {- :: vmDataVALType -} -> IO LLVMValue {- boolType* -}
boolFromVMDataVAL builder vmVal = extractFromSum builder vmVal vmDataBoolIndex

intFromVMDataVAL :: LLVMBuilder -> LLVMValue {- :: vmDataVALType -} -> IO LLVMValue {- int32Type* -}
intFromVMDataVAL builder vmVal = extractFromSum builder vmVal vmDataIntIndex

doubleFromVMDataVAL :: LLVMBuilder -> LLVMValue {- :: vmDataVALType -} -> IO LLVMValue {- doubleType* -}
doubleFromVMDataVAL builder vmVal = extractFromSum builder vmVal vmDataDoubleIndex

vmEnvFiltering :: LLVMBuilder -> LLVMValue {-:: vmFixenvType -} -> LLVMValue {- :: vmVolenvType -} -> ([Int], [Int]) {- filter -} -> IO LLVMValue {- :: vmFixenvType -}
vmEnvFiltering builder fixenv volenv (ffilter, vfilter) = do {

                                                          -- we create the result fixenv (as we know the size
                                                          ; let ressize = length ffilter + length vfilter
                                                          ; res <- createDynArray builder vmDataType (integer2LLVMInteger (fromIntegral ressize) 32)

                                                          -- we create a counter that we use for indexing the mutate in res
                                                          -- Why Alloc and not Alloca? the whole interpretation of the VM is in the same function,
                                                          -- thus an alloca will not be freed until the VM completely stopped (TODO: look if there is not alloca in helper / opcode codegen)
                                                          ; counterp <- buildAlloc builder int32Type
                                                          ; initData builder counterp

                                                          -- first loop on
                                                          ; let loop1body = \ builder val {- here an index in fixenv -} -> do {
                                                                                                                           -- we lookup the data in the fixenv
                                                                                                                           ; mdatap <- lookupDynArray builder val fixenv
                                                                                                                           ; mdata <- buildLoad builder mdatap

                                                                                                                           -- increment ref count
                                                                                                                           ; incRef builder mdata

                                                                                                                           -- save in the res
                                                                                                                           ; index <- buildLoad builder counterp
                                                                                                                           ; mutateDynArray builder index mdata res

                                                                                                                           -- increment the counter
                                                                                                                           ; nextindex <- buildAdd builder index (integer2LLVMInteger 1 32)
                                                                                                                           ; buildStore builder nextindex counterp

                                                                                                                           }
                                                          ; _ <- mapM (\ hd -> loop1body builder (integer2LLVMInteger (fromIntegral hd) 32)) ffilter


                                                          -- second loop on
                                                          ; let loop2body = \ builder val {- here an index in volenv -} -> do {
                                                                                                                           -- we lookup the data in the fixenv
                                                                                                                           ; mdata <- stackLookup builder volenv val

                                                                                                                           -- increment ref count
                                                                                                                           ; incRef builder mdata

                                                                                                                           -- save in the res
                                                                                                                           ; index <- buildLoad builder counterp
                                                                                                                           ; mutateDynArray builder index mdata res

                                                                                                                           -- increment the counter
                                                                                                                           ; nextindex <- buildAdd builder index (integer2LLVMInteger 1 32)
                                                                                                                           ; buildStore builder nextindex counterp

                                                                                                                           }

                                                          ; _ <- mapM (\ hd -> loop2body builder (integer2LLVMInteger (fromIntegral hd) 32)) vfilter

                                                          ; buildFree builder counterp

                                                          ; return res

                                                          }


mkVMDataFRAME :: LLVMBuilder -> LLVMValue -> LLVMValue -> LLVMValue -> IO LLVMValue
mkVMDataFRAME builder addr fixenv volenv = do {

                                           ; mdata <- createSum2 builder vmDataType vmDataFRAMETypeIndex
                                           ; datap <- extractFromSum builder mdata vmDataFRAMETypeIndex
                                                      
                                           -- store the return address
                                           ; maddrp <- buildStructGEP builder datap 0
                                           ; buildStore builder addr maddrp
                                                        
                                           -- store the old volenv and fixenv
                                           ; fixenvp <- buildStructGEP builder datap 1
                                           ; buildStore builder fixenv fixenvp
                                                                   
                                           ; volenvp <- buildStructGEP builder datap 2
                                           ; buildStore builder volenv volenvp
                                                                                                  
                                           ; return mdata                                                        
                                                    
                                           }

destructVMDataFRAME :: LLVMBuilder -> LLVMValue -> IO (LLVMValue, LLVMValue, LLVMValue)
destructVMDataFRAME builder framep = do {
                                    ; newlabelp <- buildStructGEP builder framep 0
                                    ; newlabel <- buildLoad builder newlabelp
                                    ; newfixenvp <- buildStructGEP builder framep 1
                                    ; newfixenv <- buildLoad builder newfixenvp
                                    ; newvolenvp <-  buildStructGEP builder framep 2
                                    ; newvolenv <- buildLoad builder newvolenvp
                                                   
                                     ; return (newlabel, newfixenv, newvolenv)
                                    }

mkVMDataREC :: LLVMBuilder -> LLVMValue -> LLVMValue -> LLVMValue -> IO LLVMValue
mkVMDataREC builder addr fixenv trigger = do {
                                          ; mdata <- createSum2 builder vmDataType vmDataRECTypeIndex
                                          ; datap <- extractFromSum builder mdata vmDataRECTypeIndex
                                                     
                                          ; maddrp <- buildStructGEP builder datap 0
                                          ; buildStore builder addr maddrp
                                                       
                                          ; mfixenvp <- buildStructGEP builder datap 1
                                          ; buildStore builder fixenv mfixenvp
                                                       
                                          ; margsp <- buildStructGEP builder datap 2
                                          ; buildStore builder trigger margsp

                                          ; return mdata
                                          }
                                                       
destructVMDataREC :: LLVMBuilder -> LLVMValue -> IO (LLVMValue, LLVMValue, LLVMValue)
destructVMDataREC builder recp = do {

                                 ; newlabelp <- buildStructGEP builder recp 0
                                 ; newlabel <- buildLoad builder newlabelp
                                               
                                 ; newfixenvp <- buildStructGEP builder recp 1
                                 ; newfixenv <- buildLoad builder newfixenvp
                                                
                                 ; triggerp <-  buildStructGEP builder recp 2
                                 ; trigger <- buildLoad builder triggerp
                                                
                                 ; return (newlabel, newfixenv, trigger)

                                 }



mkVMDataCL :: LLVMBuilder -> LLVMValue -> LLVMValue -> LLVMValue -> LLVMValue -> IO LLVMValue
mkVMDataCL builder addr fixenv volenv trigger = do {
                                                ; mdata <- createSum2 builder vmDataType vmDataCLTypeIndex
                                                ; datap <- extractFromSum builder mdata vmDataCLTypeIndex
                                                           
                                                ; maddrp <- buildStructGEP builder datap 0
                                                ; buildStore builder addr maddrp
                                                             
                                                ; mfixenvp <- buildStructGEP builder datap 1
                                                ; buildStore builder fixenv mfixenvp
                                                             
                                                ; mvolenvp <- buildStructGEP builder datap 2
                                                ; buildStore builder volenv mvolenvp
                                                             
                                                ; margsp <- buildStructGEP builder datap 3
                                                ; buildStore builder trigger margsp

                                                ; return mdata
                                                }

destructVMDataCL :: LLVMBuilder -> LLVMValue -> IO (LLVMValue, LLVMValue, LLVMValue, LLVMValue)
destructVMDataCL builder clp = do {

                                 ; newlabelp <- buildStructGEP builder clp 0
                                 ; newlabel <- buildLoad builder newlabelp
                                               
                                 ; newfixenvp <- buildStructGEP builder clp 1
                                 ; newfixenv <- buildLoad builder newfixenvp
                                                
                                 ; newvolenvp <- buildStructGEP builder clp 2
                                 ; newvolenv <- buildLoad builder newvolenvp

                                 ; triggerp <-  buildStructGEP builder clp 3
                                 ; trigger <- buildLoad builder triggerp
                                                
                                 ; return (newlabel, newfixenv, newvolenv, trigger)


                              }

mkVMDataPRIM :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue 
mkVMDataPRIM builder tag args = do {
                                ; mdata <- createSum2 builder vmDataType vmDataPRIMTypeIndex
                                ; datap <- extractFromSum builder mdata vmDataPRIMTypeIndex
                                           
                                ; tagp <- buildStructGEP builder datap 0
                                ; buildStore builder tag tagp
                                             
                                ; argsp <- buildStructGEP builder datap 1
                                ; buildStore builder args argsp
                                             
                                ; return mdata

                                }

destructVMDataPRIM :: LLVMBuilder -> LLVMValue -> IO (LLVMValue, LLVMValue)
destructVMDataPRIM builder primp = do {

                                   ; tagp <- buildStructGEP builder primp 0
                                   ; tag <- buildLoad builder tagp

                                   ; argsp <- buildStructGEP builder primp 1
                                   ; args <- buildLoad builder argsp

                                   ; return (tag, args)

                                   }

mkVMDataCONSTR :: LLVMBuilder -> LLVMValue -> LLVMValue -> IO LLVMValue 
mkVMDataCONSTR builder tag args = do {
                                ; mdata <- createSum2 builder vmDataType vmDataCONSTRTypeIndex
                                ; datap <- extractFromSum builder mdata vmDataCONSTRTypeIndex
                                           
                                ; tagp <- buildStructGEP builder datap 0
                                ; buildStore builder tag tagp
                                             
                                ; argsp <- buildStructGEP builder datap 1
                                ; buildStore builder args argsp
                                             
                                ; return mdata

                                }

destructVMDataCONSTR :: LLVMBuilder -> LLVMValue -> IO (LLVMValue, LLVMValue)
destructVMDataCONSTR builder constrp = do {

                                   ; tagp <- buildStructGEP builder constrp 0
                                   ; tag <- buildLoad builder tagp

                                   ; argsp <- buildStructGEP builder constrp 1
                                   ; args <- buildLoad builder argsp

                                   ; return (tag, args)

                                   }

-- semantics of the primitives: all the necessary data are in a stack, stored from offset offset
vmPRIMSemantics :: LLVMBuilder -> LLVMValue {- :: i8 -} -> LLVMValue {- :: vmStackType -} -> IO LLVMValue {- :: vmDataType -}
vmPRIMSemantics builder tag args = do {
                                   ; res <- buildSwitch2 builder tag [
                                             (integer2LLVMInteger (fromIntegral $ fromEnum PIEq) 8, \ builder -> 
                                                  do {
                                                  ; data1p <- stackLookup builder args (integer2LLVMInteger 0 32)
                                                  ; i1p <- valFromVMData builder data1p
                                                  ; i1 <- buildLoad builder i1p
                                                  ; i1p <- intFromVMDataVAL builder i1
                                                  ; i1 <- buildLoad builder i1p
                                                          
                                                          
                                                  ; data2p <- stackLookup builder args (integer2LLVMInteger 1 32)
                                                  ; i2p <- valFromVMData builder data2p
                                                  ; i2 <- buildLoad builder i2p
                                                  ; i2p <- intFromVMDataVAL builder i2
                                                  ; i2 <- buildLoad builder i2p
                                                          
                                                  ; res <- buildICmp builder IEQ i1 i2
                                                           
                                                  ; boolval <- createSum builder vmDataVALType vmDataBoolIndex res
                                                  ; mval <- createSum builder vmDataType vmDataVALTypeIndex boolval
                                                            
                                                  ; return mval
                                                           
                                                  }),
                                             
                                             (integer2LLVMInteger (fromIntegral $ fromEnum PISub) 8, \ builder -> 
                                                  do {
                                                  ; data1p <- stackLookup builder args (integer2LLVMInteger 0 32)
                                                  ; i1p <- valFromVMData builder data1p
                                                  ; i1 <- buildLoad builder i1p
                                                  ; i1p <- intFromVMDataVAL builder i1
                                                  ; i1 <- buildLoad builder i1p

                                                  ; data2p <- stackLookup builder args (integer2LLVMInteger 1 32)
                                                  ; i2p <- valFromVMData builder data2p
                                                  ; i2 <- buildLoad builder i2p
                                                  ; i2p <- intFromVMDataVAL builder i2
                                                  ; i2 <- buildLoad builder i2p

                                                  ; res <- buildSub builder i1 i2

                                                  ; intval <- createSum builder vmDataVALType vmDataIntIndex res
                                                  ; mval <- createSum builder vmDataType vmDataVALTypeIndex intval
                                                            
                                                  ; return mval

                                                  }),

                                             (integer2LLVMInteger (fromIntegral $ fromEnum PDAdd) 8, \ builder -> 
                                                  do {
                                                  ; data1p <- stackLookup builder args (integer2LLVMInteger 0 32)
                                                  ; d1p <- valFromVMData builder data1p
                                                  ; d1 <- buildLoad builder d1p
                                                  ; d1p <- doubleFromVMDataVAL builder d1
                                                  ; d1 <- buildLoad builder d1p

                                                  ; data2p <- stackLookup builder args (integer2LLVMInteger 1 32)
                                                  ; d2p <- valFromVMData builder data2p
                                                  ; d2 <- buildLoad builder d2p
                                                  ; d2p <- doubleFromVMDataVAL builder d2
                                                  ; d2 <- buildLoad builder d2p

                                                  ; res <- buildFAdd builder d1 d2

                                                  ; doubleval <- createSum builder vmDataVALType vmDataDoubleIndex res
                                                  ; mval <- createSum builder vmDataType vmDataVALTypeIndex doubleval
                                                            
                                                  ; return mval

                                                  })
                                             
                                            ]
                                   ; return res
                                   }

-- build the while VM exec function (toplevel)

debugVM :: Bool
debugVM = False

debugCompil :: Bool 
debugCompil = False

primitiveLLVMSemantics :: LLVMBuilder -> VMPrimitive -> [LLVMValue] {- :: vmDataVALType -} -> IO LLVMValue
primitiveLLVMSemantics builder prim args = error "Not Yet Implemented"

buildTopLevel :: LLVMModule -> CodeBlock {- code -} -> Int {- entry -} -> IO LLVMFunction {- :: vmDataVALType -}
buildTopLevel mod code entry = do {
                               -- build the toplevel execution function and the builder
                               ; toplevel <- addFunction2 mod "toplevel" $ fctType [] vmDataType

                               ; builder <- createEntryBuilder toplevel

                               ; when debugVM $ buildDebugMsg builder $ "init VM\n"
                               ; when debugCompil $ putTraceMsg $ "init VM\n"

                               -- grab the indices of the code, and build the corresponding blocks
                               ; let cindices = A.indices code
                               --; putStrLn $ "cindices = " ++ show cindices

                               -- IMPORTANT: from there we assert that vm offset and CodeBlock indices are the same

                               ; cblocks <- mapM (\ i -> createBlock builder $ "opcode " ++ show i) cindices
                               --; putStrLn $ "cblocks = " ++ show cblocks

                               -- build the exit block (the init will be entry)
                               ; exitb <- createBlock builder "exit"

                               -- create & initialize the init volenv, fixenv and stack
                               -- they need to be refered everywhere, so they are in fact pointers of ...
                               -- allocated on the stack


                               {-
                               -- this does not work --> recursive type definition ....
                               -- ...
                               -- it does now that we added the rectypes
                               -}
                               ; fixenvp <- buildAlloca builder vmFixenvType
                               ; volenvp <- buildAlloca builder vmVolenvType
                               ; stackp <- buildAlloca builder vmStackType

                               -- init fixenv is by definition empty
                               ; initfixenv <- createDynArray builder vmDataType (integer2LLVMInteger 0 32)
                               -- we init the volenv with a capacity of 10
                               ; initvolenv <- createStack builder vmDataType (integer2LLVMInteger 10 32)
                               -- we init the stack with a capacity of 20
                               ; initstack <- createStack builder vmDataType (integer2LLVMInteger 20 32)

                               ; buildStore builder initfixenv fixenvp
                               ; buildStore builder initvolenv volenvp
                               ; buildStore builder initstack stackp

                               -- we jump to the entry label
                               ; buildBr builder $ cblocks!!entry


                               -- here we generate a block which constains an exception for wrong VM offset jump
                               ; wrongoffsetjumpb <- createBlock builder "wrong offset"
                               ; moveBuilder builder wrongoffsetjumpb

                               ; _ <- buildException2 builder ("Catastrophic: VM jumped to an invalid offset !!!\n")

                               -- we now codegen the exit block
                               ; moveBuilder builder exitb

                               ; when debugVM $ buildDebugMsg builder $ "------------------ exit VM ----------------------\n"
                               ; when debugCompil $ putTraceMsg $ "------------------ exit VM ----------------------\n"

                               -- NB: if we are here, it is because the stack contains only one element
                               ; finalstack <- buildLoad builder stackp
                               ; res <- stackPop builder finalstack
                               -- we increment its counter to be sure it survive the clearing of the stack
                               ; incRef builder res

                               -- we clear the stack
                               ; destroyManagedType builder finalstack

                               -- we clear the fixenv and the volenv
                               ; finalfixenv <- buildLoad builder fixenvp
                               ; destroyManagedType builder finalfixenv

                               ; finalvolenv <- buildLoad builder volenvp
                               ; destroyManagedType builder finalvolenv

                               ; buildPrintf builder "result := " []
                               ; printVMData builder res

                               -- we return the result
                               ; buildRet builder res

                               -- now we create the codecopying for all opcode
                               ; _ <- mapM ( \ offset -> do {
                                                         -- mainly a big test case (TODO: split each case in a function for sake of readability)
                                                         ; let opcode = code!(cindices!!offset)
                                                         -- grab the corresponding block and jump to it
                                                         ; let curblock = cblocks!!(offset)
                                                         ; moveBuilder builder curblock
                                                         --; putStrLn $ "compiling: " ++ show opcode
                                                         ; case opcode of
                                                             NOP -> do {

                                                                    ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                    ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                    -- simple, we grab the next indice block and jump to it
                                                                    ; let nextblock = cblocks!!(offset+1)
                                                                    ; buildBr builder nextblock
                                                                    }
                                                             RETURN -> do {

                                                                       ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                       ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                       -- first we grab the size of the stack
                                                                       ; stack <- buildLoad builder stackp
                                                                       ; size <- stackSize builder stack

                                                                       -- the test
                                                                       ; test <- buildICmp builder IEQ size (integer2LLVMInteger 1 32)
                                                                       -- the branches
                                                                       ; closurereturnb <- createBlock builder "closurereturn"
                                                                       ; buildCondBr builder test exitb closurereturnb

                                                                       -- closurereturn: we pop the result and the frame
                                                                       -- we decref the current volenv and fixenv (meme release if not share by anybody)
                                                                       -- we update with the value of the frame
                                                                       -- we suppress the frame through buildFree because:
                                                                       --   1) as its 2 managed data will be the new current one, we avoid a incRef / decRef
                                                                       --   2) frame are never reused
                                                                       --   3) frame is just a case a sumtype
                                                                       -- push the res on top of the stack
                                                                       -- indirect jump to the proper

                                                                       ; moveBuilder builder closurereturnb

                                                                       ; res <- stackPop builder stack
                                                                       ; frame <- stackPop builder stack

                                                                       ; currvolenv <- buildLoad builder volenvp
                                                                       ; currfixenv <- buildLoad builder fixenvp
                                                                       ; decRef builder currfixenv
                                                                       ; decRef builder currvolenv

                                                                       -- this is rubbish, we should be able to automate that ...
                                                                       ; framep <- frameFromVMData builder frame

                                                                       ; (newlabel, newfixenv, newvolenv) <- destructVMDataFRAME builder framep

                                                                       ; buildStore builder newfixenv fixenvp
                                                                       ; buildStore builder newvolenv volenvp

                                                                       -- finally we free (after a cast)
                                                                       ; buildFree builder $ typeCast frame $ ptrType int8Type

                                                                       -- push the result
                                                                       ; stackPush builder stack res

                                                                       -- and jump to the good offset
                                                                       -- N.B.: should be :
                                                                       -- ; buildIndirectBr builder newlabel
                                                                       -- but storing basicblock address segfault ...

                                                                       ; buildSwitch builder newlabel (zip (map (\ i -> integer2LLVMInteger (fromIntegral i) 32) cindices) cblocks) wrongoffsetjumpb

                                                                       }
                                                             PUSH (VInt i) -> do {

                                                                              ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                              ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                              -- first we grab the size of the sttack
                                                                              ; stack <- buildLoad builder stackp

                                                                              -- we build the value
                                                                              ; intval <- createSum builder vmDataVALType vmDataIntIndex (integer2LLVMInteger (fromIntegral i) 32)
                                                                              ; mval <- createSum builder vmDataType vmDataVALTypeIndex intval

                                                                              -- store it in the stack
                                                                              ; stackPush builder stack mval

                                                                              -- jump to the next block
                                                                              ; let nextblock = cblocks!!(offset+1)
                                                                              ; buildBr builder nextblock

                                                                              }
                                                             PUSH (VDouble d) -> do {

                                                                                 ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                                 ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                                 -- first we grab the size of the sttack
                                                                                 ; stack <- buildLoad builder stackp

                                                                                 -- we build the value
                                                                                 ; intval <- createSum builder vmDataVALType vmDataDoubleIndex (double2LLVMDouble d)
                                                                                 ; mval <- createSum builder vmDataType vmDataVALTypeIndex intval

                                                                                 -- store it in the stack
                                                                                 ; stackPush builder stack mval

                                                                                 -- jump to the next block
                                                                                 ; let nextblock = cblocks!!(offset+1)
                                                                                 ; buildBr builder nextblock

                                                                                 }
                                                             PUSH (VBool b) -> do {

                                                                               ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                               ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                               -- first we grab the size of the sttack
                                                                               ; stack <- buildLoad builder stackp

                                                                               -- we build the value
                                                                               ; boolval <- createSum builder vmDataVALType vmDataBoolIndex (bool2LLVMBool b)
                                                                               ; mval <- createSum builder vmDataType vmDataVALTypeIndex boolval

                                                                               -- store it in the stack
                                                                               ; stackPush builder stack mval

                                                                               -- jump to the next block
                                                                               ; let nextblock = cblocks!!(offset+1)
                                                                               ; buildBr builder nextblock

                                                                               }
                                                             SWAP _ i -> do {

                                                                         ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                         ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                         -- a simple loop that pop on the stack and push on the volenv

                                                                         -- first we grab the stack and the volenv
                                                                         ; stack <- buildLoad builder stackp
                                                                         ; volenv <- buildLoad builder volenvp

                                                                         -- we prepare the loop body
                                                                         ; let swapbody = \ builder val -> do {

                                                                                                           -- pop from the stack
                                                                                                           ; head <- stackPop builder stack

                                                                                                           -- push on the volenv
                                                                                                           ; stackPush builder volenv head

                                                                                                           -- no reference counter update, as it did not changed
                                                                                                           ; return ()
                                                                                                           }

                                                                         -- we build the loop code here
                                                                         ; buildCounterLoop builder (integer2LLVMInteger 0 32) (integer2LLVMInteger (fromIntegral i) 32) swapbody

                                                                         -- we go to the next instruction
                                                                         ; let nextblock = cblocks!!(offset+1)
                                                                         ; buildBr builder nextblock
                                                                         }
                                                             ACCESSVOL i -> do {

                                                                            ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                            ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                            -- we grab the stack and the volenv
                                                                            ; stack <- buildLoad builder stackp
                                                                            ; volenv <- buildLoad builder volenvp

                                                                            -- we lookup the data in the volenv
                                                                            ; val <- stackLookup builder volenv (integer2LLVMInteger (fromIntegral i) 32)

                                                                            -- we need to increment its ref counter (it as one more occurence)
                                                                            ; incRef builder val

                                                                            -- we push it in the stack
                                                                            ; stackPush builder stack val

                                                                            -- we go to the next instruction
                                                                            ; let nextblock = cblocks!!(offset+1)
                                                                            ; buildBr builder nextblock

                                                                            }
                                                             ACCESSFIX i -> do {

                                                                            ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                            ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                            -- we grab the stack and the fixenv
                                                                            ; stack <- buildLoad builder stackp
                                                                            ; fixenv <- buildLoad builder fixenvp

                                                                            -- we lookup the data in the volenv
                                                                            ; valp <- lookupDynArray builder (integer2LLVMInteger (fromIntegral i) 32) fixenv 
                                                                            ; val <- buildLoad builder valp
                                                                                     
                                                                            -- we need to increment its ref counter (it as one more occurence)
                                                                            ; incRef builder val

                                                                            -- we push it in the stack
                                                                            ; stackPush builder stack val

                                                                            -- we go to the next instruction
                                                                            ; let nextblock = cblocks!!(offset+1)
                                                                            ; buildBr builder nextblock

                                                                            }
                                                             RECURSION addr name args ret filter -> do {
                                                                                                    ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                                                    ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                                                    -- we grab the volenv, the fixenv and the stack
                                                                                                    ; stack <- buildLoad builder stackp
                                                                                                    ; fixenv <- buildLoad builder fixenvp
                                                                                                    ; volenv <- buildLoad builder volenvp

                                                                                                    -- now we prepare the data in order to build the vmDataRECType

                                                                                                    -- first we get the address
                                                                                                    -- we can't use it as it seems storing address block segfault ...

                                                                                                    ; let recentryblock = cblocks!!(cindices!!addr)
                                                                                                    ; addr' <- valueFromLabel recentryblock

                                                                                                    -- then the fixenv, it is build from the current fixenv / volenv
                                                                                                    ; fixenv' <- vmEnvFiltering builder fixenv volenv filter

                                                                                                    -- the number of arguments
                                                                                                    ; let args' = integer2LLVMInteger (fromIntegral $ length args) 8

                                                                                                    -- we build the vmDataType
                                                                                                    ; mdata <- mkVMDataREC builder (integer2LLVMInteger (fromIntegral addr) 32) fixenv' args'

                                                                                                    -- and finally we push on the stack
                                                                                                    ; stackPush builder stack mdata

                                                                                                    -- we go to the next instruction
                                                                                                    ; let nextblock = cblocks!!(offset+1)
                                                                                                    ; buildBr builder nextblock


                                                                                                    }
                                                             CLOSURE addr args ret filter -> do {
                                                                                             ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                                             ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                                             -- we grab the volenv, the fixenv and the stack
                                                                                             ; stack <- buildLoad builder stackp
                                                                                             ; fixenv <- buildLoad builder fixenvp
                                                                                             ; volenv <- buildLoad builder volenvp
                                                                                                         
                                                                                             -- now we prepare the data in order to build the vmDataRECType

                                                                                             -- first we get the address
                                                                                             -- we can't use it as it seems storing address block segfault ...

                                                                                             ; let recentryblock = cblocks!!(cindices!!addr)
                                                                                             ; addr' <- valueFromLabel recentryblock
                                                                                                        
                                                                                             -- then the fixenv, it is build from the current fixenv / volenv
                                                                                             ; fixenv' <- vmEnvFiltering builder fixenv volenv filter
                                                                                           
                                                                                             -- the number of arguments
                                                                                             ; let args' = integer2LLVMInteger (fromIntegral $ length args) 8

                                                                                             -- create the volenv
                                                                                             ; volenv' <- createStack builder vmDataType $ integer2LLVMInteger (fromIntegral $ length args + 10) 32
                                                                                                           
                                                                                             -- we build the vmDataType
                                                                                             ; mdata <- mkVMDataCL builder (integer2LLVMInteger (fromIntegral addr) 32) fixenv' volenv' args'
                                                                                                          
                                                                                             -- and finally we push on the stack
                                                                                             ; stackPush builder stack mdata
                                                                                                         
                                                                                             -- we go to the next instruction
                                                                                             ; let nextblock = cblocks!!(offset+1)
                                                                                             ; buildBr builder nextblock

                                                                                             }
                                                             APPLY i -> do {
                                                                        ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                        ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                        -- first we grab the stack
                                                                        ; stack <- buildLoad builder stackp

                                                                        -- then we grab the arguments (pop from the stack and so in reverse order)
                                                                        ; revargs <- mapM (\ _ -> stackPop builder stack) [0..(i-1)]

                                                                        -- we grab the 'fct' (a vmData that should be either a REC, CL or PRIMITIVEs, other cases are errors)
                                                                        ; fct <- stackPop builder stack

                                                                        -- then we do a case analysis on fct to know the action to take
                                                                        -- as there is possible subtile memeory management, each case is responsible for managing the datas
                                                                        -- the cases are also responsible for :
                                                                        -- 1) properly set the fixenv / volenv accordingly with their own semantics
                                                                        -- 2) push the result on the stack
                                                                        -- 3) jump to the proper next block
                                                                        -- what we return is the result

                                                                        -- destructSum :: LLVMBuilder -> LLVMValue {- :: TSum tys -} -> [LLVMBuilder -> LLVMValue {- :: (tys!!n) * -} -> IO LLVMValue] -> IO LLVMValue
                                                                        ; destructSum2 builder fct [ -- the VAL case: an error
                                                                                                     (\ builder (val :: LLVMValue) -> buildException2 builder "Catastrophic: APPLY with for fct a VAL\n"),
                                                                                                     -- the PRIM case: not yet supported
                                                                                                     (\ builder (val :: LLVMValue) -> do {

                                                                                                                                      -- first we grab the capacity and size (with the applied arguments) of the arguments of the PRIM data
                                                                                                                                      ; (tag, args) <- destructVMDataPRIM builder val 

                                                                                                                                      ; argscapacity <- stackCapacity builder args
                                                                                                                                      ; argssize <- stackSize builder args
                                                                                                                                                
                                                                                                                                      ; newargssize <- buildAdd builder argssize (integer2LLVMInteger (fromIntegral i) 32)

                                                                                                                                      -- if they are equal --> we to a total apply else a partial one (because capacity of PRIM == arity)
                                                                                                                                      ; test <- buildICmp builder IEQ argscapacity newargssize
                                                                                                                                      ; partialapplyb <- createBlock builder "rec partial apply"
                                                                                                                                      ; completeapplyb <- createBlock builder "rec complete apply"

                                                                                                                                      ; buildCondBr builder test completeapplyb partialapplyb

                                                                                                                                      -- here we are in the complete application
                                                                                                                                      -- TODO: needs some cleverer code here ...
                                                                                                                                      ; moveBuilder builder completeapplyb

                                                                                                                                      -- grab the arguments
                                                                                                                                      ; _ <- mapM (\ val -> stackPush builder args val) $ reverse revargs

                                                                                                                                      -- compute the result

                                                                                                                                      ; res <- vmPRIMSemantics builder tag args

                                                                                                                                      -- pop the arguments and decref them
                                                                                                                                      ; _ <- mapM (\ _ -> do {
                                                                                                                                                          ; val <- stackPop builder args
                                                                                                                                                          ; decRef builder val
                                                                                                                                                          }
                                                                                                                                                  ) $ revargs

                                                                                                                                      -- decrement the PRIM
                                                                                                                                      ; decRef builder fct

                                                                                                                                      -- push the result and go to the next instruction
                                                                                                                                      ; stackPush builder stack res

                                                                                                                                      ; let nextblock = cblocks!!(offset+1)
                                                                                                                                      ; buildBr builder nextblock
                                                                                                                                      
                                                                                                                                      -- here we are in the partial application
                                                                                                                                      ; moveBuilder builder partialapplyb
                                                                                                                                      
                                                                                                                                      -- we recopy the args and push the new args
                                                                                                                                      ; newargs <- stackCopy builder args 

                                                                                                                                      ; _ <- mapM (\ val -> stackPush builder newargs val) $ reverse revargs

                                                                                                                                      -- create the new PRIM and initialize it
                                                                                                                                      ; mdata <- mkVMDataPRIM builder tag newargs

                                                                                                                                      -- decRef the fct
                                                                                                                                      ; decRef builder fct

                                                                                                                                      -- push the new PRIM on the stack
                                                                                                                                      ; stackPush builder stack mdata

                                                                                                                                      -- we go to the next instruction
                                                                                                                                      ; let nextblock = cblocks!!(offset+1)
                                                                                                                                      ; buildBr builder nextblock

                                                                                                                                      }
                                                                                                     ),
                                                                                                     -- the FRAME case: an error
                                                                                                     (\ builder (val :: LLVMValue) -> buildException2 builder "Catastrophic: APPLY with for fct a FRAME\n"),
                                                                                                     -- a REC case: basically two cases
                                                                                                     -- 1) complete apply
                                                                                                     -- 2) partial apply
                                                                                                     (\ builder (val :: LLVMValue) -> do {

                                                                                                                                      ; when debugCompil $ putTraceMsg $ "Apply: case " ++ show (typeOf val)

                                                                                                                                      -- here val :: vmDataRECType*
                                                                                                                                      -- we first grab the number of arguments
                                                                                                                                      ; (claddr, recfixenv, nbargs) <- destructVMDataREC builder val

                                                                                                                                      -- then we test and branch over the two cases
                                                                                                                                      -- the test being just equality
                                                                                                                                      ; test <- buildICmp builder IEQ nbargs (integer2LLVMInteger (fromIntegral i) 8)
                                                                                                                                      ; partialapplyb <- createBlock builder "rec partial apply"
                                                                                                                                      ; completeapplyb <- createBlock builder "rec complete apply"

                                                                                                                                      ; buildCondBr builder test completeapplyb partialapplyb

                                                                                                                                      -- here we are in the complete application
                                                                                                                                      ; moveBuilder builder completeapplyb

                                                                                                                                      -- basically here we need:
                                                                                                                                      -- 1) build a fixenv
                                                                                                                                      -- 2) build a volenv
                                                                                                                                      -- 3) build a frame

                                                                                                                                      -- 1) we build a new fixenv witch is the same as the one in rec extended with rec itself
                                                                                                                                      ; recfixenvsize <- dynArraySize builder recfixenv

                                                                                                                                      ; newfixenv <- copyExtDynArray builder recfixenv (integer2LLVMInteger 1 32)

                                                                                                                                      -- and place the REC as the last one (no need to increment the ref counter, as we pop it from the stack)
                                                                                                                                      ; mutateDynArray builder recfixenvsize fct newfixenv

                                                                                                                                      -- 2) build a volenv from the args (need to reverse them ...)
                                                                                                                                      --; putStrLn $ "Apply " ++ show i ++ " ==> createStack of size: fromIntegral $ length revargs + 10"
                                                                                                                                      ; newvolenv <- createStack builder vmDataType (integer2LLVMInteger (fromIntegral $ length revargs + 10) 32)
                                                                                                                                      -- still no need to incRef because they were pop from the stack
                                                                                                                                      ; _ <- mapM (\ val -> stackPush builder newvolenv val) $ reverse revargs

                                                                                                                                      -- 3) we build the frame, with the current volenv, fixenv (also no need to touch ref counters)
                                                                                                                                      ; oldvolenv <- buildLoad builder volenvp
                                                                                                                                      ; oldfixenv <- buildLoad builder fixenvp

                                                                                                                                      ; mdata <- mkVMDataFRAME builder (integer2LLVMInteger (fromIntegral $ offset + 1) 32) oldfixenv oldvolenv

                                                                                                                                      -- push the frame on the stack
                                                                                                                                      ; stackPush builder stack mdata

                                                                                                                                      -- 4) put the new fixenv and volenv as current one
                                                                                                                                      ; buildStore builder newfixenv fixenvp
                                                                                                                                      ; buildStore builder newvolenv volenvp

                                                                                                                                      -- and 5) finally jump to the recursion entry address
                                                                                                                                      ; entryaddrp <- buildStructGEP builder val 0
                                                                                                                                      ; entryaddr <- buildLoad builder entryaddrp

                                                                                                                                      ; buildSwitch builder entryaddr (zip (map (\ i -> integer2LLVMInteger (fromIntegral i) 32) cindices) cblocks) wrongoffsetjumpb

                                                                                                                                      -- here we are in the partial application
                                                                                                                                      ; moveBuilder builder partialapplyb

                                                                                                                                      -- basically here we need:
                                                                                                                                      -- 1) build a fixenv
                                                                                                                                      -- 2) build an a volenv
                                                                                                                                      -- 3) build a CL

                                                                                                                                      -- 1) we build a new fixenv witch is the same as the one in rec extended with rec itself
                                                                                                                                      ; recfixenvsize <- dynArraySize builder recfixenv

                                                                                                                                      ; newfixenv <- copyExtDynArray builder recfixenv (integer2LLVMInteger 1 32)
                                                                                                                                      
                                                                                                                                      -- and place the REC as the last one (no need to increment the ref counter, as we pop it from the stack)
                                                                                                                                      ; mutateDynArray builder recfixenvsize fct newfixenv

                                                                                                                                      -- 2) build a volenv from the args (need to reverse them ...), with the proper size
                                                                                                                                      --; putStrLn $ "Apply " ++ show i ++ " ==> createStack of size: fromIntegral $ length revargs + 10"
                                                                                                                                      ; newvolenvsize <- buildIntCast builder nbargs int32Type False
                                                                                                                                      ; newvolenv <- createStack builder vmDataType newvolenvsize
                                                                                                                                      -- still no need to incRef because they were pop from the stack
                                                                                                                                      ; _ <- mapM (\ val -> stackPush builder newvolenv val) $ reverse revargs

                                                                                                                                      -- 3) we build the CL (with the volenv, fixenv, number of missing args and address
                                                                                                                                      ; trigger <- buildSub builder nbargs (integer2LLVMInteger (fromIntegral i) 8)
                                                                                                                                      ; mdata <- mkVMDataCL builder claddr newfixenv newvolenv trigger
                                                                                                                                                   
                                                                                                                                      -- push the frame on the stack
                                                                                                                                      ; stackPush builder stack mdata

                                                                                                                                      -- we go to the next instruction
                                                                                                                                      ; let nextblock = cblocks!!(offset+1)
                                                                                                                                      ; buildBr builder nextblock

                                                                                                                                      }

                                                                                                     ),
                                                                                                     -- a CL case: not yet supported
                                                                                                     (\ builder (val :: LLVMValue) -> do {

                                                                                                                                      ; when debugCompil $ putTraceMsg $ "Apply: case " ++ show (typeOf val)

                                                                                                                                      -- here val :: vmDataCLType*
                                                                                                                                      -- we first grab the number of arguments
                                                                                                                                      ; (entryaddr, clfixenv, clvolenv, nbargs) <- destructVMDataCL builder val

                                                                                                                                      -- then we test and branch over the two cases
                                                                                                                                      -- the test being just equality
                                                                                                                                      ; test <- buildICmp builder IEQ nbargs (integer2LLVMInteger (fromIntegral i) 8)
                                                                                                                                      ; partialapplyb <- createBlock builder "cl partial apply"
                                                                                                                                      ; completeapplyb <- createBlock builder "cl complete apply"


                                                                                                                                      ; buildCondBr builder test completeapplyb partialapplyb

                                                                                                                                      -- here we are in the complete application
                                                                                                                                      ; moveBuilder builder completeapplyb

                                                                                                                                      -- TODO: need better memory management, especially depending on
                                                                                                                                      -- ref counter, we can grab directly the volenv rather than copying it

                                                                                                                                      -- 1) we copy the volenv, appending the applied arguments
                                                                                                                                      ; newvolenv <- stackCopy builder clvolenv

                                                                                                                                      ; _ <- mapM (\ val -> stackPush builder newvolenv val) $ reverse revargs

                                                                                                                                      -- we increment the counter of fixenv (so that it survive if the closure is garbage collected)
                                                                                                                                      ; incRef builder clfixenv

                                                                                                                                      -- we release the CL
                                                                                                                                      ; decRef builder fct

                                                                                                                                      -- we create a FRAME

                                                                                                                                      ; oldvolenv <- buildLoad builder volenvp
                                                                                                                                      ; oldfixenv <- buildLoad builder fixenvp

                                                                                                                                      ; mdata <- mkVMDataFRAME builder (integer2LLVMInteger (fromIntegral $ offset + 1) 32) oldfixenv oldvolenv

                                                                                                                                      -- push the frame on the stack
                                                                                                                                      ; stackPush builder stack mdata

                                                                                                                                      -- set the new fixenv and volenv to current one
                                                                                                                                      ; buildStore builder clfixenv fixenvp
                                                                                                                                      ; buildStore builder newvolenv volenvp

                                                                                                                                      -- and 5) finally jump to the recursion entry address
                                                                                                                                      ; buildSwitch builder entryaddr (zip (map (\ i -> integer2LLVMInteger (fromIntegral i) 32) cindices) cblocks) wrongoffsetjumpb

                                                                                                                                      -- here we are in the partial application
                                                                                                                                      ; moveBuilder builder partialapplyb

                                                                                                                                      -- TODO: need better memory management, especially depending on
                                                                                                                                      -- ref counter, we can grab directly the volenv rather than copying it

                                                                                                                                      -- 1) we copy the volenv, appending the applied arguments
                                                                                                                                      ; newvolenv <- stackCopy builder clvolenv

                                                                                                                                      ; _ <- mapM (\ val -> stackPush builder newvolenv val) $ reverse revargs

                                                                                                                                      -- we increment the counter of fixenv (so that it survive if the closure is garbage collected)
                                                                                                                                      ; incRef builder clfixenv

                                                                                                                                      -- we create a new CL
                                                                                                                                      ; neededargsnb <- buildSub builder nbargs (integer2LLVMInteger (fromIntegral i) 8)
                                                                                                                                      ; mdata <- mkVMDataCL builder entryaddr clfixenv newvolenv neededargsnb

                                                                                                                                      -- we release the original CL
                                                                                                                                      ; decRef builder fct

                                                                                                                                      -- push the frame on the stack
                                                                                                                                      ; stackPush builder stack mdata

                                                                                                                                      -- we go to the next instruction
                                                                                                                                      ; let nextblock = cblocks!!(offset+1)
                                                                                                                                      ; buildBr builder nextblock


                                                                                                                                      }
                                                                                                     ),
                                                                                                     -- the CONSTR Case
                                                                                                     (\ builder (val :: LLVMValue) -> do {
                                                                                                                                      -- we recopy the args and push the new args
                                                                                                                                      ; (tag, oldargs) <- destructVMDataCONSTR builder val

                                                                                                                                      ; newargs <- stackCopy builder oldargs 

                                                                                                                                      ; _ <- mapM (\ val -> stackPush builder newargs val) $ reverse revargs

                                                                                                                                      -- create the new CONSTR and initialize it
                                                                                                                                      ; mdata <- mkVMDataCONSTR builder tag newargs

                                                                                                                                      -- decRef the fct
                                                                                                                                      ; decRef builder fct

                                                                                                                                      -- push the new PRIM on the stack
                                                                                                                                      ; stackPush builder stack mdata

                                                                                                                                      -- we go to the next instruction
                                                                                                                                      ; let nextblock = cblocks!!(offset+1)
                                                                                                                                      ; buildBr builder nextblock
                                                                                                                                        
                                                                                                                                      }
                                                                                                     )
                                                                                              ]

                                                                        }
                                                             PRIMITIVE p -> do {
                                                                            ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                            ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                            -- we build the PRIM data
                                                                            ; let size = arity p
                                                                            ; args <- createStack builder vmDataType (integer2LLVMInteger (fromIntegral size) 32)
                                                                            ; mdata <- mkVMDataPRIM builder (integer2LLVMInteger (fromIntegral $ fromEnum p) 8) args

                                                                            -- push on the stack
                                                                            ; stack <- buildLoad builder stackp
                                                                            ; stackPush builder stack mdata

                                                                            -- go to the next instruction
                                                                            ; let nextblock = cblocks!!(offset+1)
                                                                            ; buildBr builder nextblock

                                                                            }
                                                             CONSTRUCTOR i _ -> do {
                                                                                ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                                ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                                -- we build the CONSTR data
                                                                                ; let size = 10
                                                                                ; args <- createStack builder vmDataType (integer2LLVMInteger (fromIntegral size) 32)
                                                                                ; mdata <- mkVMDataCONSTR builder (integer2LLVMInteger (fromIntegral $ fromEnum i) 8) args
                                                                                             
                                                                                -- push on the stack
                                                                                ; stack <- buildLoad builder stackp
                                                                                ; stackPush builder stack mdata
                                                                                            
                                                                                -- go to the next instruction
                                                                                ; let nextblock = cblocks!!(offset+1)
                                                                                ; buildBr builder nextblock

                                                                            }
                                                             TOTPRIMITIVE p -> do {

                                                                               ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                               ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                               -- we grab the stack
                                                                               ; stack <- buildLoad builder stackp

                                                                               ; args <- createStack builder vmDataType (integer2LLVMInteger (fromIntegral $ arity p) 32)

                                                                               -- we grab the proper number of data, put them on some other stack
                                                                               -- grab the arguments
                                                                               ; revargs <- mapM (\ _ -> stackPop builder stack) [0..(arity p - 1)]


                                                                               ; _ <- mapM (\ val -> do { stackPush builder args val }) $ reverse revargs


                                                                               -- we do a case analysis on the primitives and the data
                                                                               -- to create the new value and push it on the stack
                                                                               ; newval <- vmPRIMSemantics builder (integer2LLVMInteger (fromIntegral $ fromEnum p) 8) args
                                                                                                                                                                          
                                                                               ; stackPush builder stack newval

                                                                               -- destroy the temp stack (it will also decrement the args ref count)
                                                                               ; decRef builder args

                                                                               -- jump to the next opcode
                                                                               ; let nextb = cblocks!!(offset+1)
                                                                               ; buildBr builder nextb

                                                                               }
                                                             JMPC addr -> do {

                                                                          ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                          ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                          -- we grab the stack
                                                                          ; stack <- buildLoad builder stackp

                                                                          -- pop the head value
                                                                          ; head <- stackPop builder stack

                                                                          -- we extract the val from it
                                                                          ; valp <- valFromVMData builder head

                                                                          -- we get the vmDataVALType
                                                                          ; val <- buildLoad builder valp

                                                                          -- we grab a pointer to the bool
                                                                          ; boolp <- boolFromVMDataVAL builder val

                                                                          -- and finally we get the value
                                                                          ; bool <- buildLoad builder boolp

                                                                          -- now that we have the wanted data we can decrement the ref counter of the data
                                                                          ; decRef builder head

                                                                          -- we build the branching
                                                                          ; let falseb = cblocks!!(cindices!!addr)
                                                                          ; let trueb = cblocks!!(offset+1)

                                                                          ; buildCondBr builder bool trueb falseb

                                                                          }

                                                             JMP addr -> do {

                                                                         ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                         ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                         -- we just jump to the corresponding block
                                                                         ; let nextblock = cblocks!!(cindices!!addr)
                                                                         ; buildBr builder nextblock

                                                                         }

                                                             POPENV i -> do {

                                                                         ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                         ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                         -- we grab the volvenv
                                                                         ; volenv <- buildLoad builder volenvp

                                                                         -- we prepare the loop body
                                                                         ; let swapbody = \ builder val -> do {

                                                                                                           -- pop from the volenv
                                                                                                           ; head <- stackPop builder volenv

                                                                                                           -- we decrement the ref counter
                                                                                                           ; decRef builder head

                                                                                                           ; return ()
                                                                                                           }

                                                                         -- we build the loop code here
                                                                         ; buildCounterLoop builder (integer2LLVMInteger 0 32) (integer2LLVMInteger (fromIntegral i) 32) swapbody

                                                                         -- we go to the next instruction
                                                                         ; let nextblock = cblocks!!(offset+1)
                                                                         ; buildBr builder nextblock

                                                                         }

                                                             DESTRUCTOR addrs -> do {

                                                                                 ; when debugVM $ buildDebugMsg builder $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"
                                                                                 ; when debugCompil $ putTraceMsg $ show (cindices!!offset) ++ ": "  ++ show opcode ++ "\n"

                                                                                 -- we grab the volenv and the stack
                                                                                 ; volenv <- buildLoad builder volenvp
                                                                                 ; stack <- buildLoad builder stackp


                                                                                 -- we grab the top of the stack, suppose to be a CONSTR
                                                                                 ; head <- stackPop builder stack
                                                                                 ; constr <- extractFromSum builder head vmDataCONSTRTypeIndex

                                                                                 ; (tag, args) <- destructVMDataCONSTR builder constr

                                                                                 ; argssize <- stackSize builder args

                                                                                 -- we push the args on the stack
                                                                                 ; buildCounterLoop builder
                                                                                                        (integer2LLVMInteger 0 32)
                                                                                                        argssize
                                                                                                        (\ builder val -> do {
                                                                                                                          ; mdata <- stackLookup builder args val
                                                                                                                          ; incRef builder mdata
                                                                                                                          ; stackPush builder volenv mdata
                                                                                                                          }
                                                                                                        )

                                                                                 -- we decref the CONSTR
                                                                                 ; decRef builder head

                                                                                 -- we build the switch
                                                                                 --buildSwitch :: LLVMBuilder -> LLVMValue -> [(LLVMValue, LLVMBlock)] -> LLVMBlock -> IO ()
                                                                                 ; destructerror <- createBlock builder "destructerror"
                                                                                                     
                                                                                 ; buildSwitch builder tag (map (\ i -> (integer2LLVMInteger (fromIntegral i) 8, cblocks!!(addrs!!i))) [0..(length addrs - 1)]) destructerror

                                                                                 ; moveBuilder builder destructerror
                                                                                 ; buildException2 builder ("CONSTR tag does not have destructor ...")

                                                                                 }

                                                             _ -> error $ "buildTopLevel: opcode not yet supported, " ++ show opcode

                                                         }
                                           ) [0..(length cindices - 1)]

                               ; return toplevel
                               }


printVMData :: LLVMBuilder -> LLVMValue {- :: vmDataType -} -> IO ()
printVMData builder value = do {
                            ; destructSum3 builder value [ 
                                                (\ builder (val :: LLVMValue) -> 
                                                     do {
                                                     ; val <- buildLoad builder val
                                                     ; destructSum3 builder val [ 
                                                                         (\ builder val -> do {
                                                                                           ; val <- buildLoad builder val
                                                                                           ; buildPrintf builder "%d" [val]
                                                                                           }
                                                                         ),
                                                                         (\ builder val -> do {
                                                                                           ; val <- buildLoad builder val
                                                                                           ; buildPrintf builder "%g" [val]
                                                                                           }
                                                                         ),
                                                                         (\ builder val -> do {
                                                                                           ; val <- buildLoad builder val
                                                                                           ; buildPrintf builder "%d" [val]
                                                                                           }
                                                                         )
                                                                        ]
                                                     }
                                                ),
                                                (\ builder (val :: LLVMValue) -> buildPrintf builder "PRIM" []),
                                                (\ builder (val :: LLVMValue) -> buildPrintf builder "FRAME" []),
                                                (\ builder (val :: LLVMValue) -> buildPrintf builder "REC" []),
                                                (\ builder (val :: LLVMValue) -> buildPrintf builder "CL" []),
                                                (\ builder (val :: LLVMValue) -> buildPrintf builder "CONSTR" [])
                                               ]
                            ; buildPrintf builder "\n" []
                            }