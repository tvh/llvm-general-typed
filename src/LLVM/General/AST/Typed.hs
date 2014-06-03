{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module LLVM.General.AST.Typed where

import Data.Singletons
import Data.Singletons.TH
import Data.Promotion.Prelude hiding (Nat)
import Data.Word

import Data.HList

import Data.Number.Binary

import qualified LLVM.General.AST.AddrSpace as L
import qualified LLVM.General.AST.Type as L
import qualified LLVM.General.AST.Float as LF
import qualified LLVM.General.AST.Name as L
import qualified LLVM.General.AST.Constant as LC
import qualified LLVM.General.AST.Operand as LO
import qualified LLVM.General.AST.Instruction as LI
import qualified LLVM.General.AST.IntegerPredicate as LIP
import qualified LLVM.General.AST.FloatingPointPredicate as LFP
import qualified LLVM.General.AST.RMWOperation as LR

class ToUnTyped a b where
  unTyped :: a -> b

instance Integral a => ToUnTyped Binary a where
  unTyped = fromBinary

instance (Functor f, ToUnTyped a b) => ToUnTyped (f a) (f b) where
  unTyped = fmap unTyped

instance (ToUnTyped a b) => ToUnTyped (a,c) (b,c) where
  unTyped (x,y) = (unTyped x, y)

instance ToUnTyped (HList '[]) [b] where
  unTyped HNil = []
instance (ToUnTyped (HList xs) [b], ToUnTyped a b) => ToUnTyped (HList (a ': xs)) [b] where
  unTyped (HCons x xs) = unTyped x:unTyped xs

data Vect (n::Binary) a where
  VNil  :: Vect Zero a
  VCons :: a -> Vect n a -> Vect (Succ n) a

instance ToUnTyped a b => ToUnTyped (Vect n a) [b] where
  unTyped VNil = []
  unTyped (VCons x xs) = unTyped x:unTyped xs

data AddrSpace = AddrSpace Binary

instance ToUnTyped AddrSpace L.AddrSpace where
  unTyped (AddrSpace n) = L.AddrSpace (unTyped n)

data Type
  = VoidType
  | IntegerType { typeBits :: Binary }
  | PointerType { pointerReferent :: Type, pointerAddrSpace :: AddrSpace }
  | FloatingPointType { typeBits :: Binary, floatingPointFormat :: L.FloatingPointFormat }
  | FunctionType { resultType :: Type, argumentTypes :: [Type], isVarArg :: Bool }
  | VectorType { nVectorElements :: Binary, elementType :: Type }
  | StructureType { elementTypes :: [Type] }
  | ArrayType { nArrayElements :: Binary, elementType :: Type }
  
instance ToUnTyped Type L.Type where
  unTyped VoidType = L.VoidType
  unTyped IntegerType{..} = L.IntegerType $ unTyped typeBits
  unTyped PointerType{..} = L.PointerType (unTyped pointerReferent) (unTyped pointerAddrSpace)
  unTyped FloatingPointType{..} = L.FloatingPointType (unTyped typeBits) floatingPointFormat
  unTyped FunctionType{..} = L.FunctionType (unTyped resultType) (unTyped argumentTypes) isVarArg
  unTyped VectorType{..} = L.VectorType (unTyped nVectorElements) (unTyped elementType)
  unTyped StructureType{..} = L.StructureType False (unTyped elementTypes)
  unTyped ArrayType{..} = L.ArrayType (unTyped nArrayElements) (unTyped elementType)

data SomeFloat t where
  Single :: Float -> SomeFloat (FloatingPointType (U 32) L.IEEE)
  Double :: Double -> SomeFloat (FloatingPointType (U 64) L.IEEE)

type family InnerTypes a where
  InnerTypes '[] = '[]
  InnerTypes (c a ': xs) = a ': InnerTypes xs

data Constant (a :: Type) where
  Int :: { integerValue :: Integer }
    -> Constant (IntegerType n)
  Float :: (a ~ FloatingPointType b c) => { floatValue :: SomeFloat a }
    -> Constant a
  Null :: Constant a
  Struct :: (InnerTypes xs ~ a, ToUnTyped (HList xs) [LC.Constant]) => { structName :: Maybe L.Name, memberValuesS :: HList xs }
    -> Constant (StructureType a)
  Array :: SingI a => { memberValuesA :: Vect n (Constant a) }
    -> Constant (ArrayType n a)
  Vector :: SingI a => { memberValuesV :: Vect n (Constant a) }
    -> Constant (VectorType n a)
  Undef :: Constant a
  GlobalReference :: L.Name
    -> Constant a

instance SingI a => ToUnTyped (Constant a) LC.Constant where
  unTyped x@Int{..} =
    let IntegerType n = fromSing $ singByProxy x
    in LC.Int (unTyped n) integerValue
  unTyped (Float x) =
    LC.Float $ case x of
      Single f -> LF.Single f
      Double d -> LF.Double d      
  unTyped x@Null =
    LC.Null $ unTyped $ fromSing $ singByProxy x
  unTyped Struct{..} =
    LC.Struct structName False (unTyped memberValuesS)
  unTyped x@Array{..} =
    let ArrayType _n t = fromSing $ singByProxy x
    in LC.Array (unTyped t) (unTyped memberValuesA)
  unTyped Vector{..} = LC.Vector (unTyped memberValuesV)
  unTyped x@Undef =
    LC.Undef $ unTyped $ fromSing $ singByProxy x
  unTyped (GlobalReference name) =
    LC.GlobalReference name

data Operand (a::Type) where
  LocalReference :: L.Name -> Operand a
  ConstantOperand :: Constant a -> Operand a

instance SingI a => ToUnTyped (Operand a) LO.Operand where
  unTyped (LocalReference  n) = LO.LocalReference n
  unTyped (ConstantOperand c) = LO.ConstantOperand $ unTyped c

promoteOnly [d|
  isFloatTy :: Type -> Bool
  isFloatTy FloatingPointType{} = True
  isFloatTy VectorType{elementType = FloatingPointType{}} = True
               
  isIntTy :: Type -> Bool
  isIntTy IntegerType{} = True
  isIntTy VectorType{elementType = IntegerType{}} = True

  smallerIntTy :: Type -> Type -> Bool
  smallerIntTy (IntegerType b1) (IntegerType b2) = b1 < b2
  smallerIntTy v1 v2 =
    let VectorType n1 t1 = v1
        VectorType n2 t2 = v2
        IntegerType b1 = t1
        IntegerType b2 = t2
    in n1 == n2 && b1 < b2

  smallerFloatTy :: Type -> Type -> Bool
  smallerFloatTy (FloatingPointType b1 _) (FloatingPointType b2 _) = b1 < b2
  smallerFloatTy v1 v2 =
    let VectorType n1 t1 = v1
        VectorType n2 t2 = v2
        FloatingPointType b1 _ = t1
        FloatingPointType b2 _ = t2
    in n1 == n2 && b1 < b2

  intFpCast :: Type -> Type -> Bool
  intFpCast IntegerType{} FloatingPointType{} = True
  intFpCast v1 v2 =
    let VectorType n1 IntegerType{}       = v1
        VectorType n2 FloatingPointType{} = v2
    in n1 == n2

  ptrIntCast :: Type -> Type -> Bool
  ptrIntCast PointerType{} IntegerType{} = True
  ptrIntCast v1 v2 =
    let VectorType n1 PointerType{} = v1
        VectorType n2 IntegerType{} = v2
    in n1 == n2

  ptrAddrSpaceDifferent :: Type -> Type -> Bool
  ptrAddrSpaceDifferent (PointerType t1 s1) (PointerType t2 s2) = t1 == t2 && s1 /= s2

  iCmpRes :: Type -> Type -> Bool
  iCmpRes IntegerType{} (IntegerType n) = fromBinary n == 1
  iCmpRes (VectorType n1 IntegerType{}) (VectorType n2 (IntegerType n)) = fromBinary n == 1 && n1 == n2

  fCmpRes :: Type -> Type -> Bool
  fCmpRes FloatingPointType{} (IntegerType n) = fromBinary n == 1
  fCmpRes (VectorType n1 FloatingPointType{}) (VectorType n2 (IntegerType n)) = fromBinary n == 1 && n1 == n2

  selectable :: Type -> Type -> Bool
  selectable (IntegerType n) _ = fromBinary n == 1
  selectable (VectorType n1 (IntegerType n)) (VectorType n2 _) = fromBinary n == 1 && n1 == n2

  extractTy :: Type -> [Binary] -> Type
  extractTy t ns@(_:_) = extractTy' t ns

  extractTy' :: Type -> [Binary] -> Type
  extractTy' t [] = t
  extractTy' t (n:ns) =
    case t of
      (ArrayType n1 t') -> if n1 > n then extractTy' t' ns else error "array out of bounds"
      (StructureType ts) -> extractTy' (ts `index` n) ns
  |]

data Instruction a where
  Add :: (IsIntTy a ~ True) => { 
      nsw :: Bool,
      nuw :: Bool,
      operand0 :: Operand a,
      operand1 :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  FAdd :: (IsFloatTy a ~ True) => {
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a,
      operand1 :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Sub :: (IsIntTy a ~ True) => {
      nsw :: Bool,
      nuw :: Bool,
      operand0 :: Operand a,
      operand1 :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  FSub :: (IsFloatTy a ~ True) => { 
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Mul :: (IsIntTy a ~ True) => { 
      nsw :: Bool, 
      nuw :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata 
    } -> Instruction a
  FMul :: (IsFloatTy a ~ True) => { 
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  UDiv :: (IsIntTy a ~ True) => { 
      exact :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  SDiv :: (IsIntTy a ~ True) => { 
      exact :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  FDiv :: (IsFloatTy a ~ True) => { 
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  URem :: (IsIntTy a ~ True) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  SRem :: (IsIntTy a ~ True) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  FRem :: (IsFloatTy a ~ True) => { 
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Shl :: (IsIntTy a ~ True) => { 
      nsw :: Bool, 
      nuw :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  LShr :: (IsIntTy a ~ True) => { 
      exact :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  AShr :: (IsIntTy a ~ True) => { 
      exact :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  And :: (IsIntTy a ~ True) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Or :: (IsIntTy a ~ True) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Xor :: (IsIntTy a ~ True) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Alloca :: (SingI b, a ~ IntegerType b) => { 
      numElements :: Maybe (Operand a),
      alignmentA :: Word32,
      metadataAlloca :: LI.InstructionMetadata
    } -> Instruction (PointerType ty addrspace)
  Load :: SingI addrspace => {
      volatile :: Bool, 
      addressLoad :: Operand (PointerType a addrspace),
      maybeAtomicityLoad :: Maybe LI.Atomicity,
      alignmentL :: Word32,
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Store :: (SingI addrspace, SingI a) => {
      volatile' :: Bool, 
      addressStore :: Operand (PointerType a addrspace),
      value :: Operand a,
      maybeAtomicityStore :: Maybe LI.Atomicity,
      alignment :: Word32,
      metadataVoid :: LI.InstructionMetadata
    } -> Instruction VoidType
  -- TODO: unify types
  GetElementPtr :: (SingI s, SingI a, ToUnTyped (HList idxs) [LO.Operand]) => { 
      inBounds :: Bool,
      addressG :: Operand (PointerType a s),
      indices :: HList idxs,
      metadataG :: LI.InstructionMetadata
    } -> Instruction (PointerType b s)
  Fence :: { 
      atomicityF :: LI.Atomicity,
      metadataVoid :: LI.InstructionMetadata 
    } -> Instruction VoidType
  CmpXchg :: (SingI addrspace) => { 
      volatileC :: Bool,
      address :: Operand (PointerType a addrspace),
      expected :: Operand a,
      replacement :: Operand a,
      atomicity :: LI.Atomicity,
      metadata :: LI.InstructionMetadata 
    } -> Instruction a
  AtomicRMW :: (SingI addrspace) => { 
      volatile :: Bool,
      rmwOperation :: LR.RMWOperation,
      address :: Operand (PointerType a addrspace),
      value' :: Operand a,
      atomicity :: LI.Atomicity,
      metadata :: LI.InstructionMetadata 
    } -> Instruction a
  Trunc :: (SingI a, SmallerIntTy b a ~ True) => { 
      operand :: Operand a,
      metadata :: LI.InstructionMetadata 
    } -> Instruction b
  ZExt :: (SingI a, SmallerIntTy a b ~ True) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata 
    } -> Instruction b
  SExt :: (SingI a, SmallerIntTy a b ~ True) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FPToUI :: (SingI a, IntFpCast b a ~ True ) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FPToSI :: (SingI a, IntFpCast b a ~ True ) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  UIToFP :: (SingI a, IntFpCast a b ~ True ) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  SIToFP :: (SingI a, IntFpCast a b ~ True ) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FPTrunc :: (SingI a, SmallerFloatTy b a ~ True) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FPExt :: (SingI a, SmallerFloatTy a b ~ True) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  PtrToInt :: (SingI a, PtrIntCast a b ~ True) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  IntToPtr :: (SingI a, PtrIntCast b a ~ True) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
-- TODO: TypeCheck
  BitCast :: (SingI a) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  AddrSpaceCast :: (SingI a, PtrAddrSpaceDifferent a b ~ True) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  ICmp :: (SingI a, ICmpRes a b ~ True) => {
      iPredicate :: LIP.IntegerPredicate,
      operand0' :: Operand a,
      operand1' :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FCmp :: (SingI a, FCmpRes a b ~ True) => {
      fpPredicate :: LFP.FloatingPointPredicate,
      operand0' :: Operand a,
      operand1' :: Operand a,
      metadata :: LI.InstructionMetadata
    }-> Instruction b
  Phi :: {
      incomingValues :: [ (Operand a, L.Name) ],
      metadata :: LI.InstructionMetadata
  } -> Instruction a
{-
  Call :: {
      isTailCall :: Bool,
      callingConvention :: CallingConvention,
      returnAttributes :: [ParameterAttribute],
      function :: CallableOperand,
      arguments :: [(Operand, [ParameterAttribute])],
      functionAttributes :: [FunctionAttribute],
      metadata :: LI.InstructionMetadata
  } -> Instruction a
-}
  Select :: (SingI a, Selectable a b ~ True) => { 
      condition' :: Operand a,
      trueValue :: Operand b,
      falseValue :: Operand b,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
{-
  VAArg :: { 
      argList :: Operand,
      type' :: Type,
      metadata :: LI.InstructionMetadata 
    } -> Instruction a
-}
  ExtractElement :: (SingI n, SingI b, IsIntTy b ~ True) => { 
      vectorExtract :: Operand (VectorType n a),
      indexExtract :: Operand b,
      metadata :: LI.InstructionMetadata 
    } -> Instruction a
  InsertElement :: (SingI a, SingI b, IsIntTy b ~ True) => { 
      vectorInsert :: Operand (VectorType n a),
      elementE :: Operand a,
      indexInsert :: Operand b,
      metadataVect :: LI.InstructionMetadata
    } -> Instruction (VectorType n a)
  ShuffleVector :: (SingI a, SingI n, SingI m, u32 ~ U 32, SingI u32) => { 
      operand0'' :: Operand (VectorType n a),
      operand1'' :: Operand (VectorType n a),
      mask :: Constant (VectorType m (IntegerType u32)),
      metadataVect :: LI.InstructionMetadata
    } -> Instruction (VectorType m a)
  ExtractValue :: (SingI a, SingI idxs, ExtractTy a idxs ~ b) => { 
      aggregateE :: Operand a,
      indices' :: Proxy idxs,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  InsertValue :: (SingI b, SingI idxs, ExtractTy a idxs ~ b) => { 
      aggregateV :: Operand a,
      elementV :: Operand b,
      indices' :: Proxy idxs,
      metadata :: LI.InstructionMetadata
    } -> Instruction a
{-
  LandingPad :: { 
      type' :: Type,
      personalityFunction :: Operand,
      cleanup :: Bool,
      clauses :: [LandingPadClause],
      metadata :: LI.InstructionMetadata 
    } -> Instruction a
-}

instance SingI a => ToUnTyped (Instruction a) LI.Instruction where
  unTyped Add{..}           = LI.Add nsw nuw (unTyped operand0) (unTyped operand1) metadata
  unTyped FAdd{..}          = LI.FAdd fastMathFlags (unTyped operand0) (unTyped operand1) metadata
  unTyped Sub{..}           = LI.Sub nsw nuw (unTyped operand0) (unTyped operand1) metadata
  unTyped FSub{..}          = LI.FSub fastMathFlags (unTyped operand0) (unTyped operand1) metadata
  unTyped Mul{..}           = LI.Mul nsw nuw (unTyped operand0) (unTyped operand1) metadata
  unTyped FMul{..}          = LI.FMul fastMathFlags (unTyped operand0) (unTyped operand1) metadata
  unTyped UDiv{..}          = LI.UDiv exact (unTyped operand0) (unTyped operand1) metadata
  unTyped SDiv{..}          = LI.SDiv exact (unTyped operand0) (unTyped operand1) metadata
  unTyped FDiv{..}          = LI.FDiv fastMathFlags (unTyped operand0) (unTyped operand1) metadata
  unTyped URem{..}          = LI.URem (unTyped operand0) (unTyped operand1) metadata
  unTyped SRem{..}          = LI.SRem (unTyped operand0) (unTyped operand1) metadata
  unTyped FRem{..}          = LI.FRem fastMathFlags (unTyped operand0) (unTyped operand1) metadata
  unTyped Shl{..}           = LI.Shl nsw nuw (unTyped operand0) (unTyped operand1) metadata
  unTyped LShr{..}          = LI.LShr exact (unTyped operand0) (unTyped operand1) metadata
  unTyped AShr{..}          = LI.AShr exact (unTyped operand0) (unTyped operand1) metadata
  unTyped And{..}           = LI.And (unTyped operand0) (unTyped operand1) metadata
  unTyped Or{..}            = LI.Or (unTyped operand0) (unTyped operand1) metadata
  unTyped Xor{..}           = LI.Xor (unTyped operand0) (unTyped operand1) metadata
  unTyped x@Alloca{..}      =
    let PointerType t _ = fromSing $ singByProxy x
    in LI.Alloca (unTyped t) (unTyped numElements) alignmentA metadataAlloca
  unTyped Load{..}          = LI.Load volatile (unTyped addressLoad) maybeAtomicityLoad alignmentL metadata
  unTyped Store{..}         = LI.Store volatile' (unTyped addressStore) (unTyped value) maybeAtomicityStore alignment metadataVoid
  unTyped GetElementPtr{..} = LI.GetElementPtr inBounds (unTyped addressG) (unTyped indices) metadataG
  unTyped Fence{..}         = LI.Fence atomicityF metadataVoid
  unTyped CmpXchg{..}       = LI.CmpXchg volatileC (unTyped address) (unTyped expected) (unTyped replacement) atomicity metadata
  unTyped AtomicRMW{..}     = LI.AtomicRMW volatile rmwOperation (unTyped address) (unTyped value') atomicity metadata
  unTyped x@Trunc{..}       =
    let t = fromSing $ singByProxy x
    in LI.Trunc (unTyped operand) (unTyped t) metadata
  unTyped x@ZExt{..}        =
    let t = fromSing $ singByProxy x
    in LI.ZExt (unTyped operand) (unTyped t) metadata
  unTyped x@SExt{..}        =
    let t = fromSing $ singByProxy x
    in LI.SExt (unTyped operand) (unTyped t) metadata
  unTyped x@FPToUI{..}      =
    let t = fromSing $ singByProxy x
    in LI.FPToUI (unTyped operand) (unTyped t) metadata
  unTyped x@FPToSI{..}      =
    let t = fromSing $ singByProxy x
    in LI.FPToSI (unTyped operand) (unTyped t) metadata
  unTyped x@UIToFP{..}      =
    let t = fromSing $ singByProxy x
    in LI.UIToFP (unTyped operand) (unTyped t) metadata
  unTyped x@SIToFP{..}      =
    let t = fromSing $ singByProxy x
    in LI.SIToFP (unTyped operand) (unTyped t) metadata
  unTyped x@FPTrunc{..}     =
    let t = fromSing $ singByProxy x
    in LI.FPTrunc (unTyped operand) (unTyped t) metadata
  unTyped x@FPExt{..}       =
    let t = fromSing $ singByProxy x
    in LI.FPExt (unTyped operand) (unTyped t) metadata
  unTyped x@PtrToInt{..}    =
    let t = fromSing $ singByProxy x
    in LI.PtrToInt (unTyped operand) (unTyped t) metadata
  unTyped x@IntToPtr{..}    =
    let t = fromSing $ singByProxy x
    in LI.IntToPtr (unTyped operand) (unTyped t) metadata
  unTyped x@BitCast{..}     =
    let t = fromSing $ singByProxy x
    in LI.BitCast (unTyped operand) (unTyped t) metadata
  unTyped x@AddrSpaceCast{..} =
    let t = fromSing $ singByProxy x
    in LI.AddrSpaceCast (unTyped operand) (unTyped t) metadata
  unTyped ICmp{..}            = LI.ICmp iPredicate (unTyped operand0') (unTyped operand1') metadata
  unTyped FCmp{..}            = LI.FCmp fpPredicate (unTyped operand0') (unTyped operand1') metadata
  unTyped x@Phi{..}           =
    let t = fromSing $ singByProxy x
    in LI.Phi (unTyped t) (unTyped incomingValues) metadata
  unTyped Select{..}          = LI.Select (unTyped condition') (unTyped trueValue) (unTyped falseValue) metadata
  unTyped ExtractElement{..}  = LI.ExtractElement (unTyped vectorExtract) (unTyped indexExtract) metadata
  unTyped InsertElement{..}   = LI.InsertElement (unTyped vectorInsert) (unTyped elementE) (unTyped indexInsert) metadataVect
  unTyped ShuffleVector{..}   = LI.ShuffleVector (unTyped operand0'') (unTyped operand1'') (unTyped mask) metadataVect
  unTyped ExtractValue{..}    =
    let idxs = fromSing $ singByProxy indices'
    in LI.ExtractValue (unTyped aggregateE) (unTyped idxs) metadata
  unTyped InsertValue{..}     =
    let idxs = fromSing $ singByProxy indices'
    in LI.InsertValue (unTyped aggregateV) (unTyped elementV) (unTyped idxs) metadata

data Terminator where
  Ret :: (SingI a) => { 
      returnOperand :: Maybe (Operand a),
      metadata' :: LI.InstructionMetadata
    } -> Terminator
  CondBr :: (SingI a) => { 
      condition :: Operand a, 
      trueDest :: L.Name, 
      falseDest :: L.Name,
      metadata' :: LI.InstructionMetadata
    } -> Terminator
  Br :: { 
      dest :: L.Name,
      metadata' :: LI.InstructionMetadata
    } -> Terminator
  Switch :: (SingI a) => {
      operand' :: Operand a,
      defaultDest :: L.Name,
      dests :: [(Constant a, L.Name)],
      metadata' :: LI.InstructionMetadata
    } -> Terminator
  IndirectBr :: (SingI a) => {
      operand' :: Operand a,
      possibleDests :: [L.Name],
      metadata' :: LI.InstructionMetadata
    } -> Terminator
{-
  Invoke :: {
      callingConvention' :: CallingConvention,
      returnAttributes' :: [ParameterAttribute],
      function' :: CallableOperand,
      arguments' :: [(Operand, [ParameterAttribute])],
      functionAttributes' :: [FunctionAttribute],
      returnDest :: Name,
      exceptionDest :: Name,
      metadata' :: InstructionMetadata
    } -> Terminator
-}
  Resume :: (SingI a) => {
      operand' :: Operand a,
      metadata' :: LI.InstructionMetadata
    } -> Terminator
  Unreachable :: {
      metadata' :: LI.InstructionMetadata
    } -> Terminator

instance ToUnTyped Terminator LI.Terminator where
  unTyped Ret{..} = LI.Ret (unTyped returnOperand) metadata'
  unTyped CondBr{..} = LI.CondBr (unTyped condition) trueDest falseDest metadata'
  unTyped Br{..} = LI.Br dest metadata'
  unTyped Switch{..} = LI.Switch (unTyped operand') defaultDest (unTyped dests) metadata'
  unTyped IndirectBr{..} = LI.IndirectBr (unTyped operand') possibleDests metadata'
  unTyped Resume{..} = LI.Resume (unTyped operand') metadata'
  unTyped Unreachable{..} = LI.Unreachable metadata'  

instance ToUnTyped a b => ToUnTyped (LI.Named a) (LI.Named b) where
  unTyped (n LI.:= x) = n LI.:= unTyped x
  unTyped (LI.Do x)   = LI.Do $ unTyped x
  
genSingletons [
  ''AddrSpace,
  ''L.FloatingPointFormat,
  ''Type
  ]
