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

import Data.Singletons.Prelude
import Data.Singletons.TypeLits
import Data.Singletons.TH
import Data.Word

import Data.HList

--import Data.Number.Binary

import qualified LLVM.General.AST as L
import qualified LLVM.General.AST.Linkage as L
import qualified LLVM.General.AST.DataLayout as L
import qualified LLVM.General.AST.CallingConvention as L
import qualified LLVM.General.AST.InlineAssembly as L
import qualified LLVM.General.AST.Visibility as L
import qualified LLVM.General.AST.Attribute as L
import qualified LLVM.General.AST.AddrSpace as L
import qualified LLVM.General.AST.Float as LF
import qualified LLVM.General.AST.Constant as LC
import qualified LLVM.General.AST.Operand as LO
import qualified LLVM.General.AST.Instruction as LI
import qualified LLVM.General.AST.IntegerPredicate as LIP
import qualified LLVM.General.AST.FloatingPointPredicate as LFP
import qualified LLVM.General.AST.RMWOperation as LR

class ToUnTyped a b where
  unTyped :: a -> b

instance (Functor f, ToUnTyped a b) => ToUnTyped (f a) (f b) where
  unTyped = fmap unTyped

instance (ToUnTyped a b) => ToUnTyped (a,c) (b,c) where
  unTyped (x,y) = (unTyped x, y)

instance ToUnTyped (HList '[]) [b] where
  unTyped HNil = []
instance (ToUnTyped (HList xs) [b], ToUnTyped a b) => ToUnTyped (HList (a ': xs)) [b] where
  unTyped (HCons x xs) = unTyped x:unTyped xs

data Vect (n::Nat) a where
  VNil  :: Vect 0 a
  VCons :: a -> Vect n a -> Vect (n :+ 1) a

instance ToUnTyped a b => ToUnTyped (Vect n a) [b] where
  unTyped VNil = []
  unTyped (VCons x xs) = unTyped x:unTyped xs

data AddrSpace a = AddrSpace a

instance Integral a => ToUnTyped (AddrSpace a) L.AddrSpace where
  unTyped (AddrSpace n) = L.AddrSpace (fromIntegral n)

data Type a
  = VoidType
  | IntegerType { typeBits :: a }
  | PointerType { pointerReferent :: Type a, pointerAddrSpace :: AddrSpace a }
  | FloatingPointType { typeBits :: a, floatingPointFormat :: L.FloatingPointFormat }
  | FunctionType { resultType :: Type a, argumentTypes :: [Type a], isVarArg :: Bool }
  | VectorType { nVectorElements :: a, elementType :: Type a }
  | StructureType { isPacked :: Bool, elementTypes :: [Type a] }
  | ArrayType { nArrayElements :: a, elementType :: Type a }
  | MetadataType
  
instance ToUnTyped (Type Integer) L.Type where
  unTyped VoidType = L.VoidType
  unTyped IntegerType{..} = L.IntegerType $ fromInteger typeBits
  unTyped PointerType{..} = L.PointerType (unTyped pointerReferent) (unTyped pointerAddrSpace)
  unTyped FloatingPointType{..} = L.FloatingPointType (fromInteger typeBits) floatingPointFormat
  unTyped FunctionType{..} = L.FunctionType (unTyped resultType) (unTyped argumentTypes) isVarArg
  unTyped VectorType{..} = L.VectorType (fromInteger nVectorElements) (unTyped elementType)
  unTyped StructureType{..} = L.StructureType isPacked (unTyped elementTypes)
  unTyped ArrayType{..} = L.ArrayType (fromInteger nArrayElements) (unTyped elementType)
  unTyped MetadataType = L.MetadataType

genSingletons [
  ''AddrSpace,
  ''L.FloatingPointFormat,
  ''Type
  ]

data SomeFloat t where
  Single :: Float -> SomeFloat (FloatingPointType 32 L.IEEE)
  Double :: Double -> SomeFloat (FloatingPointType 64 L.IEEE)

type family InnerTypes a where
  InnerTypes '[] = '[]
  InnerTypes (c a ': xs) = a ': InnerTypes xs

data Constant a where
  Int :: { integerValue :: Integer }
    -> Constant (IntegerType n)
  Float :: (a ~ FloatingPointType b c) => { floatValue :: SomeFloat a }
    -> Constant a
  Null :: Constant a
  Struct :: (InnerTypes xs ~ a, ToUnTyped (HList xs) [LC.Constant]) => { structName :: Maybe L.Name, memberValuesS :: HList xs }
    -> Constant (StructureType packed a)
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
    in LC.Int (fromInteger n) integerValue
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

data Operand a where
  LocalReference :: L.Name -> Operand a
  ConstantOperand :: Constant a -> Operand a

instance SingI a => ToUnTyped (Operand a) LO.Operand where
  unTyped (LocalReference  n) = LO.LocalReference n
  unTyped (ConstantOperand c) = LO.ConstantOperand $ unTyped c

data CallableOperand t where
  Inline :: L.InlineAssembly -> CallableOperand (FunctionType resType argTypes varArg)
  CallableOperand :: SingI (FunctionType resType argTypes varArg) => Operand (FunctionType resType argTypes varArg) -> CallableOperand (FunctionType resType argTypes varArg)

instance ToUnTyped (CallableOperand t) LO.CallableOperand where
  unTyped (Inline inline) = Left inline
  unTyped (CallableOperand op) = Right (unTyped op)

promoteOnly [d|
  bitSize :: Type Nat -> Nat
  bitSize t =
    case t of
      VoidType            -> 0
      IntegerType{}       -> typeBits t
      FloatingPointType{} -> typeBits t
      VectorType{..}      -> nVectorElements * bitSize elementType

  iCmpRes :: Type Nat -> Type Nat
  iCmpRes IntegerType{} = IntegerType 1
  iCmpRes (VectorType n IntegerType{}) = VectorType n (IntegerType 1)

  fCmpRes :: Type Nat -> Type Nat
  fCmpRes FloatingPointType{} = IntegerType 1
  fCmpRes (VectorType n FloatingPointType{}) = VectorType n (IntegerType 1)
 
  index :: [a] -> Nat -> a
  index (x:_) 0 = x
  index (_:xs) n = index xs (n - 1)
  
  extractTy :: Type Nat -> [Nat] -> Type Nat
  extractTy t ns@(_:_) = extractTy' t ns

  extractTy' :: Type Nat -> [Nat] -> Type Nat
  extractTy' t [] = t
  extractTy' t (n:ns) =
    case t of
      (ArrayType n1 t') -> if n1 > n then extractTy' t' ns else error "array out of bounds"
      (StructureType  _ ts) -> extractTy' (ts `index` n) ns
  |]

class SmallerIntTy (a :: Type Nat) (b :: Type Nat)
instance ((b1 :< b2) ~ True) => SmallerIntTy (IntegerType b1) (IntegerType b2)
instance ((b1 :< b2) ~ True) => SmallerIntTy (VectorType n (IntegerType b1)) (VectorType n (IntegerType b2))

class SmallerFloatTy (a :: Type Nat) (b :: Type Nat)
instance ((b1 :< b2) ~ True) => SmallerFloatTy (FloatingPointType b1 f1) (FloatingPointType b2 f2)
instance ((b1 :< b2) ~ True) => SmallerFloatTy (VectorType n (FloatingPointType b1 f1)) (VectorType n (FloatingPointType b2 f2))

class IntFpCast (a :: Type Nat) (b :: Type Nat)
instance IntFpCast (IntegerType n1) (FloatingPointType n2 f)
instance IntFpCast (VectorType n (IntegerType n1)) (VectorType n (FloatingPointType n2 f))

class PtrAddrSpaceDifferent (a :: Type Nat) (b :: Type Nat)
instance ((s1 :/= s2) ~ True) => PtrAddrSpaceDifferent (PointerType t s1) (PointerType t s2)

class PtrIntCast (a :: Type Nat) (b :: Type Nat)
instance PtrIntCast (PointerType t s) (IntegerType n)
instance PtrIntCast (VectorType n (PointerType t s)) (VectorType n2 (IntegerType n))

class Selectable (a :: Type Nat) (b :: Type Nat)
instance Selectable (IntegerType 1) b
instance Selectable (VectorType n (IntegerType 1)) (VectorType n b)

class IsFloatTy (ty :: Type Nat)
instance IsFloatTy (FloatingPointType bits format)
instance IsFloatTy (VectorType n (FloatingPointType bits format))

class IsIntTy (ty :: Type Nat)
instance IsIntTy (IntegerType bits)
instance IsIntTy (VectorType n (IntegerType bits))

class ToUnTyped (HList args) [(LO.Operand, [L.ParameterAttribute])] => ValidArgs (types :: [Type Nat]) (varArg :: Bool) (args :: [*])
instance ValidArgs '[] a '[]
instance (SingI t, ValidArgs '[] True xs) => ValidArgs '[]        True   ((Operand t, [L.ParameterAttribute]) ': xs)
instance (SingI t, ValidArgs ts varArg xs) => ValidArgs (t ': ts) varArg ((Operand t, [L.ParameterAttribute]) ': xs)

data Instruction a where
  Add :: (IsIntTy a) => { 
      nsw :: Bool,
      nuw :: Bool,
      operand0 :: Operand a,
      operand1 :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  FAdd :: (IsFloatTy a) => {
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a,
      operand1 :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Sub :: (IsIntTy a) => {
      nsw :: Bool,
      nuw :: Bool,
      operand0 :: Operand a,
      operand1 :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  FSub :: (IsFloatTy a) => { 
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Mul :: (IsIntTy a) => { 
      nsw :: Bool, 
      nuw :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata 
    } -> Instruction a
  FMul :: (IsFloatTy a) => { 
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  UDiv :: (IsIntTy a) => { 
      exact :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  SDiv :: (IsIntTy a) => { 
      exact :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  FDiv :: (IsFloatTy a) => { 
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  URem :: (IsIntTy a) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  SRem :: (IsIntTy a) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  FRem :: (IsFloatTy a) => { 
      fastMathFlags :: LI.FastMathFlags,
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Shl :: (IsIntTy a) => { 
      nsw :: Bool, 
      nuw :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  LShr :: (IsIntTy a) => { 
      exact :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  AShr :: (IsIntTy a) => { 
      exact :: Bool, 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  And :: (IsIntTy a) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Or :: (IsIntTy a) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Xor :: (IsIntTy a) => { 
      operand0 :: Operand a, 
      operand1 :: Operand a, 
      metadata :: LI.InstructionMetadata
    } -> Instruction a
  Alloca :: (SingI a) => { 
      numElements :: Maybe (Operand (IntegerType a)),
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
  Trunc :: (SingI a, SmallerIntTy b a) => { 
      operand :: Operand a,
      metadata :: LI.InstructionMetadata 
    } -> Instruction b
  ZExt :: (SingI a, SmallerIntTy a b) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata 
    } -> Instruction b
  SExt :: (SingI a, SmallerIntTy a b) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FPToUI :: (SingI a, IntFpCast b a) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FPToSI :: (SingI a, IntFpCast b a) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  UIToFP :: (SingI a, IntFpCast a b) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  SIToFP :: (SingI a, IntFpCast a b) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FPTrunc :: (SingI a, SmallerFloatTy b a) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FPExt :: (SingI a, SmallerFloatTy a b) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  PtrToInt :: (SingI a, PtrIntCast a b) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  IntToPtr :: (SingI a, PtrIntCast b a) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  BitCast :: (SingI a, bitSize a ~ bitSize b) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  AddrSpaceCast :: (SingI a, PtrAddrSpaceDifferent a b) => {
      operand :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  ICmp :: (SingI a, ICmpRes a ~ b) => {
      iPredicate :: LIP.IntegerPredicate,
      operand0' :: Operand a,
      operand1' :: Operand a,
      metadata :: LI.InstructionMetadata
    } -> Instruction b
  FCmp :: (SingI a, FCmpRes a ~ b) => {
      fpPredicate :: LFP.FloatingPointPredicate,
      operand0' :: Operand a,
      operand1' :: Operand a,
      metadata :: LI.InstructionMetadata
    }-> Instruction b
  Phi :: {
      incomingValues :: [ (Operand a, L.Name) ],
      metadata :: LI.InstructionMetadata
  } -> Instruction a
  Call :: (ValidArgs argTypes varArg args) => {
      isTailCall :: Bool,
      callingConvention :: L.CallingConvention,
      returnAttributes :: [L.ParameterAttribute],
      function :: CallableOperand (FunctionType resType argTypes varArg),
      arguments :: HList args,
      functionAttributes :: [L.FunctionAttribute],
      metadata :: LI.InstructionMetadata
  } -> Instruction resType
  Select :: (SingI a, Selectable a b) => { 
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
  ExtractElement :: (SingI n, SingI b, IsIntTy b) => { 
      vectorExtract :: Operand (VectorType n a),
      indexExtract :: Operand b,
      metadata :: LI.InstructionMetadata 
    } -> Instruction a
  InsertElement :: (SingI a, SingI b, IsIntTy b) => { 
      vectorInsert :: Operand (VectorType n a),
      elementE :: Operand a,
      indexInsert :: Operand b,
      metadataVect :: LI.InstructionMetadata
    } -> Instruction (VectorType n a)
  ShuffleVector :: (SingI a, SingI n, SingI m) => { 
      operand0'' :: Operand (VectorType n a),
      operand1'' :: Operand (VectorType n a),
      mask :: Constant (VectorType m (IntegerType 32)),
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
  unTyped Call{..}            = LI.Call isTailCall callingConvention returnAttributes (unTyped function) (unTyped arguments) functionAttributes metadata
  unTyped Select{..}          = LI.Select (unTyped condition') (unTyped trueValue) (unTyped falseValue) metadata
  unTyped ExtractElement{..}  = LI.ExtractElement (unTyped vectorExtract) (unTyped indexExtract) metadata
  unTyped InsertElement{..}   = LI.InsertElement (unTyped vectorInsert) (unTyped elementE) (unTyped indexInsert) metadataVect
  unTyped ShuffleVector{..}   = LI.ShuffleVector (unTyped operand0'') (unTyped operand1'') (unTyped mask) metadataVect
  unTyped ExtractValue{..}    =
    let idxs = fromSing $ singByProxy indices'
    in LI.ExtractValue (unTyped aggregateE) (map fromInteger idxs) metadata
  unTyped InsertValue{..}     =
    let idxs = fromSing $ singByProxy indices'
    in LI.InsertValue (unTyped aggregateV) (unTyped elementV) (map fromInteger idxs) metadata

data Terminator a where
  Ret :: (SingI a) => { 
      returnOperand :: Maybe (Operand a),
      metadata' :: LI.InstructionMetadata
    } -> Terminator VoidType
  CondBr :: (SingI a) => { 
      condition :: Operand a, 
      trueDest :: L.Name, 
      falseDest :: L.Name,
      metadata' :: LI.InstructionMetadata
    } -> Terminator VoidType
  Br :: { 
      dest :: L.Name,
      metadata' :: LI.InstructionMetadata
    } -> Terminator VoidType
  Switch :: (SingI a) => {
      operand' :: Operand a,
      defaultDest :: L.Name,
      dests :: [(Constant a, L.Name)],
      metadata' :: LI.InstructionMetadata
    } -> Terminator VoidType
  IndirectBr :: (SingI a) => {
      operand' :: Operand a,
      possibleDests :: [L.Name],
      metadata' :: LI.InstructionMetadata
    } -> Terminator VoidType
  Invoke :: (ValidArgs argTypes varArg args) => {
      callingConvention' :: L.CallingConvention,
      returnAttributes' :: [L.ParameterAttribute],
      function' :: CallableOperand (FunctionType resType argTypes varArg),
      arguments' :: HList args,
      functionAttributes' :: [L.FunctionAttribute],
      returnDest :: L.Name,
      exceptionDest :: L.Name,
      metadata'' :: LI.InstructionMetadata
    } -> Terminator resType
  Resume :: (SingI a) => {
      operand' :: Operand a,
      metadata' :: LI.InstructionMetadata
    } -> Terminator VoidType
  Unreachable :: {
      metadata' :: LI.InstructionMetadata
    } -> Terminator VoidType

instance ToUnTyped (Terminator a) LI.Terminator where
  unTyped Ret{..} = LI.Ret (unTyped returnOperand) metadata'
  unTyped CondBr{..} = LI.CondBr (unTyped condition) trueDest falseDest metadata'
  unTyped Br{..} = LI.Br dest metadata'
  unTyped Switch{..} = LI.Switch (unTyped operand') defaultDest (unTyped dests) metadata'
  unTyped IndirectBr{..} = LI.IndirectBr (unTyped operand') possibleDests metadata'
  unTyped Invoke{..} = LI.Invoke callingConvention' returnAttributes' (unTyped function') (unTyped arguments') functionAttributes' returnDest exceptionDest metadata''
  unTyped Resume{..} = LI.Resume (unTyped operand') metadata'
  unTyped Unreachable{..} = LI.Unreachable metadata'  

instance Functor LI.Named where
  fmap f (LI.Do x)   = LI.Do (f x)
  fmap f (n LI.:= x) = n LI.:= (f x)
  
data BasicBlock where
  BasicBlock :: (ToUnTyped (HList xs) [LI.Named LI.Instruction]) => {
    blockName :: L.Name,
    blockInstructions :: HList xs,
    blockTerminator :: LI.Named (Terminator a)
  } -> BasicBlock

instance ToUnTyped BasicBlock L.BasicBlock where
  unTyped BasicBlock{..} = L.BasicBlock blockName (unTyped blockInstructions) (unTyped blockTerminator)

data Parameter (a :: Type Nat) where
  Parameter :: (SingI a) => {
    parameterName :: L.Name,
    parameterAttributes :: [L.ParameterAttribute]
  } -> Parameter a

instance ToUnTyped (Parameter a) L.Parameter where
  unTyped x@Parameter{..} =
    let t = fromSing $ singByProxy x
    in L.Parameter (unTyped t) parameterName parameterAttributes

data Global (a :: Type Nat) where
  GlobalVariable :: SingI a => {
    name :: L.Name,
    linkage :: L.Linkage,
    visibility :: L.Visibility,
    isThreadLocal :: Bool,
    addrSpace :: AddrSpace Word32,
    hasUnnamedAddr :: Bool,
    isConstant :: Bool,
    initializer :: Maybe (Constant a),
    section :: Maybe String,
    globalAlignment :: Word32
  } -> Global a
  GlobalAlias :: SingI a => {
    name :: L.Name,
    linkage :: L.Linkage,
    visibility :: L.Visibility,
    aliasee :: Constant a
  } -> Global a
  Function :: (ToUnTyped (HList params) [L.Parameter], InnerTypes params ~ args) => {
    linkage' :: L.Linkage,
    visibility' :: L.Visibility,
    callingConventionF :: L.CallingConvention,
    returnAttributesF :: [L.ParameterAttribute],
    name' :: L.Name,
    parameters :: HList params,
    functionAttributesF :: [L.FunctionAttribute],
    section' :: Maybe String,
    globalAlignment' :: Word32,
    garbageCollectorName :: Maybe String,
    basicBlocks :: [BasicBlock]
  } -> Global (FunctionType a args varArg)

instance SingI a => ToUnTyped (Global a) L.Global where
  unTyped x@GlobalVariable{..} =
    let t = fromSing $ singByProxy x
    in L.GlobalVariable name linkage visibility isThreadLocal (unTyped addrSpace) hasUnnamedAddr isConstant (unTyped t) (unTyped initializer) section globalAlignment
  unTyped x@GlobalAlias{..} =
    let t = fromSing $ singByProxy x
    in L.GlobalAlias name linkage visibility (unTyped t) (unTyped aliasee)
  unTyped x@Function{..} =
    let FunctionType retType _ varArg = fromSing $ singByProxy x
    in L.Function linkage' visibility' callingConventionF returnAttributesF (unTyped retType) name' (unTyped parameters, varArg) functionAttributesF section' globalAlignment' garbageCollectorName (unTyped basicBlocks)

data Definition where
  GlobalDefinition :: ToUnTyped (Global a) L.Global => Global a -> Definition
  TypeDefinition :: (SingI a) => L.Name -> Proxy (a :: Maybe (Type Nat)) -> Definition
  MetadataNodeDefinition :: ToUnTyped (HList defs) [Maybe LO.Operand] => LO.MetadataNodeID -> HList defs -> Definition
  NamedMetadataDefinition :: String -> [LO.MetadataNodeID] -> Definition
  ModuleInlineAssembly :: String -> Definition

instance ToUnTyped Definition L.Definition where
  unTyped (GlobalDefinition g) = L.GlobalDefinition (unTyped g)
  unTyped (TypeDefinition name t) =
    let mTy = fromSing $ singByProxy t
    in L.TypeDefinition name (unTyped mTy)
  unTyped (MetadataNodeDefinition nodeId defs) = L.MetadataNodeDefinition nodeId (unTyped defs)
  unTyped (NamedMetadataDefinition name ids) = L.NamedMetadataDefinition name ids
  unTyped (ModuleInlineAssembly assembly) = L.ModuleInlineAssembly assembly

data Module = 
  Module {
    moduleName :: String,
    moduleDataLayout :: Maybe L.DataLayout,
    moduleTargetTriple :: Maybe String,
    moduleDefinitions :: [Definition]
  } 

instance ToUnTyped Module L.Module where
  unTyped Module{..} = L.Module moduleName moduleDataLayout moduleTargetTriple (unTyped moduleDefinitions)
