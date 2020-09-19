{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Exercises where

import Data.Kind (Type, Constraint)
import Data.Function ((&))
import Prelude hiding ((!!))
import GHC.TypeLits hiding (Nat)
import Data.Type.Equality
import Unsafe.Coerce
import Debug.Trace



{- ONE -}

-- | One of the restrictions around classes that we occasionally hit is that we
-- can only have one instance for a type. There are, for example, two good
-- candidates for a monoid instance when we think about 'Integer':

data IntegerMonoid = Sum | Product

-- | a. Write a newtype around 'Integer' that lets us choose which instance we
-- want.
type role MyInt phantom
newtype MyInt (mon :: IntegerMonoid) = MyInt Int

--newtype Additive       = Additive Int
--newtype Multiplicative = Multiplicative Int

-- | b. Write the two monoid instances for 'Integer'.
instance Semigroup (MyInt Sum) where
  (<>) (MyInt a) (MyInt b) = MyInt (a + b)
instance Semigroup (MyInt Product) where
  (<>) (MyInt a) (MyInt b) = MyInt (a * b)

instance Monoid (MyInt Sum) where
  mempty = MyInt 0
instance Monoid (MyInt Product) where
  mempty = MyInt 1

-- | c. Why do we need @FlexibleInstances@ to do this?





{- TWO -}

-- | We can write a type that /is/ of kind 'Type', but has no value-level
-- members. We usually call this type 'Void':

data Void -- No constructors!

-- | a. If we promote this with DataKinds, can we produce any /types/ of kind
-- 'Void'?

-- Kind        Void
-- Type  Void  ----
-- Term  ----  ----

-- | b. What are the possible type-level values of kind 'Maybe Void'?

-- Kind                       Maybe Void
-- Type  Maybe Void           Nothing
-- Term  Just --- | Nothing   -----------

--tstJustVoid :: Maybe Void
--tstJustVoid = Just undefined
--
--tst33 :: Maybe Void -> String
--tst33 (Just a) = ""

-- | c. Considering 'Maybe Void', and similar examples of kinds such as
-- 'Either Void Bool', why do you think 'Void' might be a useful kind?
-- A a | B b | C Void




{- THREE -}

-- | a. Write a GADT that holds strings or integers, and keeps track of how
-- many strings are present. Note that you might need more than 'Nil' and
-- 'Cons' this time...

data Nat = Z | S Nat

data StringAndIntList (stringCount :: Nat) where
  SNil :: StringAndIntList 'Z
  ConsInt :: Int -> StringAndIntList n -> StringAndIntList n
  ConstStr :: String -> StringAndIntList n -> StringAndIntList ('S n)

-- | b. Update it to keep track of the count of strings /and/ integers.
data StringAndIntList2 (stringCount :: Nat) (intCount :: Nat) where
  SNil2 :: StringAndIntList2 'Z 'Z
  ConsInt2 :: Int -> StringAndIntList2 n m -> StringAndIntList2 n ('S m)
  ConstStr2 :: String -> StringAndIntList2 n m -> StringAndIntList2 ('S n) m


-- | c. What would be the type of the 'head' function?
head' :: StringAndIntList2 n m -> Maybe (Either Int String)
head' SNil2 = Nothing
head' (ConsInt2 n _) = Just (Left n)
head' (ConstStr2 s _) = Just (Right s)

--head' :: StringAndIntList2 'Z m       -> Maybe Int
--head' :: StringAndIntList2 'Z ('S m)  -> Int
--head' :: StringAndIntList2 n 'Z       -> Maybe String
--head' :: StringAndIntList2 ('S n) 'Z  -> String
--head' :: StringAndIntList2 ('S n) ('S m)  -> Either Int String


{- FOUR -}

-- | When we talked about GADTs, we discussed existentials, and how we could
-- only know something about our value if the context told us:

data Showable where
  Showable :: Show a => a -> Showable

-- | a. Write a GADT that holds something that may or may not be showable, and
-- stores this fact in the type-level.

data MaybeShowable (isShowable :: Bool) where
  ShowableTrue  :: Show a => a -> MaybeShowable 'True
  ShowableFalse ::           a -> MaybeShowable 'False

-- | b. Write a 'Show' instance for 'MaybeShowable'. Your instance should not
-- work unless the type is actually 'show'able.

instance Show (MaybeShowable b) where
  show (ShowableTrue a) = "ShowableTrue " ++ show a
  show (ShowableFalse _) = "ShowableFalse"

-- | c. What if we wanted to generalise this to @Constrainable@, such that it
-- would work for any user-supplied constraint of kind 'Constraint'? How would
-- the type change? What would the constructor look like? Try to build this
-- type - GHC should tell you exactly which extension you're missing.

data Constrainable (c :: Type -> Constraint) where
  Constr :: c a => a -> Constrainable c

foo :: Constrainable Show -> String
foo (Constr a) = show a


{- FIVE -}

-- | Recall our list type:

data List a = Nil | Cons a (List a)

-- | a. Use this to write a better 'HList' type than we had in the @GADTs@
-- exercise. Bear in mind that, at the type-level, 'Nil' and 'Cons' should be
-- "ticked". Remember also that, at the type-level, there's nothing weird about
-- having a list of types!

data HList (types :: [Type]) where
   HNil  :: HList '[]                         -- HList 'Nil
   HCons :: a -> HList ts -> HList (a ': ts)  -- HList ('Cons a ts)

instance Show (HList '[]) where
  show HNil = trace "nil" "HNil"

instance (Show t, Show (HList ts)) => Show (HList (t ': ts)) where
  show (HCons a ts) = trace "cons" $ "HCons " ++ show a ++ " " ++ show ts


-- | b. Write a well-typed, 'Maybe'-less implementation for the 'tail' function
-- on 'HList'.
htail :: HList (t ': ts) -> HList ts
htail (HCons _ t) = t

-- | c. Could we write the 'take' function? What would its type be? What would
-- get in our way?

type        TakeTF :: Nat -> [Type] -> [Type]
type family TakeTF n ts where
  TakeTF _ '[] = '[]
  TakeTF 'Z _ = '[]
  TakeTF (S n) (t ': ts) = t ': TakeTF n ts
  TakeTF _ _ = TypeError (Text "TakeTF Error")

type TFTail :: [Type] -> [Type]
type family TFTail ts where
  TFTail (t ': ts) = ts
  TFTail _ = TypeError (Text "TFTail Error")

type        Dec :: Nat -> Maybe Nat
type family Dec n where
  Dec ('S n) = 'Just n
  Dec 'Z = 'Nothing

--class MaybeParse (a :: Maybe Nat) where
--  type ProxT a :: Type
--  isJustP :: Maybe (ProxT a)
--
--instance MaybeParse 'Nothing where
--  type ProxT 'Nothing = Proxy Void
--  isJustP = Nothing
--
--instance MaybeParse ('Just n) where
--  type ProxT ('Just n) = Proxy n
--  isJustP = Just (Proxy @n)
--
--type Two = 'S ('S Z)
--
--tstMaybeParse :: MaybeParse (Dec Two) => Proxy (Dec Two) -> String
--tstMaybeParse p = case isJustP of
--  Nothing -> "n"
--  Just pp -> "j"


type Length :: [k] -> Nat
type family Length ts where
  Length '[] = 'Z
  Length (_ ': ts) = 'S (Length ts)

-- ts :: a : []
-- n  :: S S Z

data LessOrEq (n :: Nat) where
  LZ :: LessOrEq n
  LS :: LessOrEq n -> LessOrEq ('S n)

type ToNat :: LessOrEq n -> Nat
type family ToNat n where
  ToNat 'LZ = 'Z
  ToNat ('LS n) = 'S (ToNat n)

type LEQ :: Nat -> Nat -> Bool
type family LEQ n m where
  LEQ 'Z _      = 'True
  LEQ ('S n) ('S m)  = LEQ n m
  LEQ _ _  = 'False

--proof :: forall n a ts ts1 .
--      (ts :~: (a ': ts1)) -> (TakeTF n ts) :~: (a : TakeTF (Dec n) ts1)
--proof Refl = unsafeCoerce Refl
--
--proof2 :: forall (n :: Nat) (ts :: [Type]) (t :: Type) (tail :: [Type]) .
--  (ts ~ (t ': tail)) =>
--  LEQ n (Length ts) :~: 'True -> LEQ (Dec n) (Length tail) :~: 'True
--proof2 Refl = unsafeCoerce Refl

--class TakeAble (ts :: [Type]) (n :: LessOrEq (Length ts)) where
--  type ResT ts n :: [Type]
--  take :: HList ts -> Proxy n -> HList (ResT ts n)
--
--instance TakeAble ts LZ where
--  type ResT _ LZ = '[]
--  take _ _ = HNil
--
--instance TakeAble (t ': ts) n where
--  type ResT (t ': ts) (LS i) = t ': ResT ts i

--htake :: forall (ts :: [Type])  (n :: Nat) .
--          (LEQ n (Length ts) ~ 'True) =>
--          HList ts -> Proxy n -> HList (TakeTF n ts)
--htake HNil _ = HNil
--htake (HCons a ts) _ = case (proof @n @_ @ts @_ Refl , proof2 @n @ts @_ @_ Refl) of
--  (Refl, Refl) -> HCons a (htake ts (Proxy @(Dec n)))

--htake HNil _ = HNil
--htake (HCons a ts) _ = case isJustP @(Dec n) @_ of
--  Nothing -> undefined -- HCons a HNil
--  Just p -> undefined -- HCons a (unsafeCoerce $ htake (unsafeCoerce ts) (unsafeCoerce p))



--hlist = (HCons 5 (HCons "dasd" (HCons 25 (HCons 25 (HCons 25 HNil)))))
--
--tsthtake :: HList '[Int, String]
--tsthtake = htake hlist (Proxy @('S ('S 'Z)))


{- SIX -}

-- | Here's a boring data type:

--data BlogAction
--  = AddBlog
--  | DeleteBlog
--  | AddComment
--  | DeleteComment

-- | a. Two of these actions, 'DeleteBlog' and 'DeleteComment', should be
-- admin-only. Extend the 'BlogAction' type (perhaps with a GADT...) to
-- express, at the type-level, whether the value is an admin-only operation.
-- Remember that, by switching on @DataKinds@, we have access to a promoted
-- version of 'Bool'!

data BlogAction (isSafe :: Bool) where
  AddBlog :: BlogAction 'True
  DeleteBlog :: BlogAction 'False
  AddComment :: BlogAction 'True
  DeleteComment :: BlogAction 'False

-- | b. Write a 'BlogAction' list type that requires all its members to be
-- the same "access level": "admin" or "non-admin".

data BlogActionList (isSafe :: Bool) where
  BALNil :: BlogActionList b
  BALCons :: BlogAction b -> BlogActionList b -> BlogActionList b

-- | c. Let's imagine that our requirements change, and 'DeleteComment' is now
-- available to a third role: moderators. Could we use 'DataKinds' to introduce
-- the three roles at the type-level, and modify our type to keep track of
-- this?





{- SEVEN -}

-- | When we start thinking about type-level Haskell, we inevitably end up
-- thinking about /singletons/. Singleton types have a one-to-one value-type
-- correspondence - only one value for each type, only one type for each value.
-- A simple example is '()', whose only value is '()'. 'Bool' is /not/ a
-- singleton, because it has multiple values.

-- We can, however, /build/ a singleton type for 'Bool':

data SBool (value :: Bool) where
  SFalse :: SBool 'False
  STrue  :: SBool 'True

-- | a. Write a singleton type for natural numbers:

data SNat (value :: Nat) where
  SZero :: SNat 'Z
  SSucc :: SNat n -> SNat ('S n)

-- | b. Write a function that extracts a vector's length at the type level:

length' :: Vector n a -> SNat n
length' VNil = SZero
length' (VCons _ t) = SSucc (length' t)

-- | c. Is 'Proxy' a singleton type?

data Proxy a = Proxy





{- EIGHT -}

-- | Let's imagine we're writing some Industry Haskell™, and we need to read
-- and write to a file. To do this, we might write a data type to express our
-- intentions:

data Program (fileOpen :: Bool) result where
  OpenFile   :: Program b result -> Program b result
  WriteFile  :: String -> Program b result -> Program b result
  ReadFile   :: (String -> Program b result) -> Program b result
  CloseFile  :: Program True result -> Program False result
  Exit       :: result -> Program True result

-- | We could then write a program like this to use our language:

myApp :: Program False Bool
myApp
  = OpenFile $ WriteFile "HEY" $ (ReadFile $ \contents ->
      if contents == "WHAT"
        then CloseFile            $ Exit True
        else WriteFile "... bug?" $ CloseFile $ Exit False)

-- | ... but wait, there's a bug! If the contents of the file equal "WHAT", we
-- forget to close the file! Ideally, we would like the compiler to help us: we
-- could keep track of whether the file is open at the type level!
--
-- - We should /not/ be allowed to open a file if another file is currently
-- open.
--
-- - We should /not/ be allowed to close a file unless a file is open.
--
-- If we had this at the type level, the compiler should have been able to tell
-- us that the branches of the @if@ have different types, and this program
-- should never have made it into production. We should also have to say in the
-- type of 'myApp' that, once the program has completed, the file will be
-- closed.

-- | Improve the 'Program' type to keep track of whether a file is open.  Make
-- sure the constructors respect this flag: we shouldn't be able to read or
-- write to the file unless it's open. This exercise is a bit brain-bending;
-- why? How could we make it more intuitive to write?

-- | EXTRA: write an interpreter for this program. Nothing to do with data
-- kinds, but a nice little problem.

--interpret :: Program {- ??? -} a -> IO a
--interpret = error "Implement me?"





{- NINE -}

-- | Recall our vector type:

data Vector (n :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | Imagine we want to write the '(!!)' function for this vector. If we wanted
-- to make this type-safe, and avoid 'Maybe', we'd have to have a type that can
-- only hold numbers /smaller/ than some type-level value.

-- | a. Implement this type! This might seem scary at first, but break it down
-- into Z and S cases. That's all the hint you need :)

data SmallerThan (limit :: Nat) where
  SZ :: SmallerThan ('S n)
  SS :: SmallerThan n -> SmallerThan ('S n)

-- | b. Write the '(!!)' function:
(!!) :: Vector n a -> SmallerThan n -> a
(!!) (VCons a _) SZ = a
(!!) (VCons _ t) (SS n) = t !! n
(!!) VNil _ = error "Impossible!"


-- | c. Write a function that converts a @SmallerThan n@ into a 'Nat'.
toNat :: SmallerThan n -> Nat
toNat SZ = Z
toNat (SS n) = S (toNat n)



tst :: SmallerThan ('S ('S ('S 'Z)))
tst = (SS (SS SZ))

--tst2 = VNil !! SZ
--tst2 = VCons 5 VNil !! SS SZ