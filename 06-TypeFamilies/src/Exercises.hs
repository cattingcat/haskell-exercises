{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Exercises where

import Data.Kind (Constraint, Type)

-- | Before we get started, let's talk about the @TypeOperators@ extension. All
-- this does is allow us to write types whose names are operators, and write
-- regular names as infix names with the backticks, as we would at the value
-- level.





{- ONE -}

data Nat = Z | S Nat

-- | a. Use the @TypeOperators@ extension to rewrite the 'Add' family with the
-- name '+':
type family (+) (a :: Nat) (b :: Nat) where
  (+) 'Z     n = n
  (+) ('S n) m = 'S (n + m)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?
type family (*) (a :: Nat) (b :: Nat) where
  (*) 'Z     n = 'Z
  (*) ('S n) m = m + (n * m)

data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.
add :: SNat n -> SNat m -> SNat (n + m)
add SZ n = n
add (SS n) m = SS (add n m)




{- TWO -}

data Vector (count :: Nat) (a :: Type) where
  VNil  :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?

append :: Vector m a -> Vector n a -> Vector (m + n) a
append VNil        v = v
append (VCons a u) v = VCons a (append u v)



-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.

flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n * m) b
flatMap VNil _ = VNil
flatMap (VCons a v) f = append (f a) (flatMap v f)





{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type family (&&) (a :: Bool) (b :: Bool) where
  (&&) 'True 'True = 'True
  (&&) _     _     = 'False

-- | b. Write the type-level @||@ function for booleans.
type family (||) (a :: Bool) (b :: Bool) where
  (||) 'False 'False = 'False
  (||) _      _      = 'True


-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type family All (bs :: [Bool]) where
  All '[] = 'True
  All (b ': bs) = b && All bs




{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.
type family Compare (a :: Nat) (b :: Nat) :: Ordering where
  Compare 'Z 'Z = EQ
  Compare ('S _) 'Z = GT
  Compare 'Z ('S _) = LT
  Compare ('S n) ('S m) = Compare n m

-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max a b = ProcessOrd a b (Compare a b)

type family ProcessOrd (a :: Nat) (b :: Nat) (org :: Ordering) :: Nat where
  ProcessOrd a b EQ = a
  ProcessOrd a b GT = a
  ProcessOrd a b LT = b

-- | c. Write a family to get the maximum natural in a list.
type family MaxList (ls :: [Nat]) :: Nat where
  MaxList '[] = 'Z
  MaxList (a ': as) = Max a (MaxList as)




{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.

type family Insert (n :: Nat) (tree :: Tree) :: Tree where
  Insert n Empty = Node Empty n Empty
  Insert n (Node l m r) = Insert' (Compare n m) l r m n

type        Insert' :: Ordering -> Tree -> Tree -> Nat -> Nat -> Tree
type family Insert' ord l r n m where
  Insert' GT l r n m =  Node l m (Insert n r)
  Insert' EQ l r n m =  Node l m (Insert n r)
  Insert' LT l r n m =  Node (Insert n l) m r

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Delete (n :: Nat) (tree :: Tree) :: Tree where
  Delete n Empty = Empty
  Delete n (Node l m r) = Delete' (Compare n m) l r n m

type        Delete' :: Ordering -> Tree -> Tree -> Nat -> Nat -> Tree
type family Delete' ord l r n m where
  Delete' GT l r n m =  Node l m (Delete n r)
  Delete' LT l r n m =  Node (Delete n l) m r
  Delete' _  l r _ _ =  CombineTrees l r

type family CombineTrees (t1 :: Tree) (t2 :: Tree) :: Tree where
  CombineTrees Empty t = t
  CombineTrees t Empty = t
  CombineTrees (Node l1 n1 r1) (Node l2 n2 r2) = CombineTrees' (Compare n1 n2) (Node l1 n1 r1) (Node l2 n2 r2)

type family CombineTrees' (ord :: Ordering) (t1 :: Tree) (t2 :: Tree) where
  CombineTrees' LT t1 (Node l m r) = Node (CombineTrees t1 l) m r
  CombineTrees' EQ t1 (Node l m r) = Node (CombineTrees t1 l) m r
  CombineTrees' GT t1 (Node l m r) = Node l m (CombineTrees t1 r)

{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.

data HList (xs :: [Type]) where
  HNil  :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Write a function that appends two 'HList's.
type family Append (as :: [Type]) (bs :: [Type]) :: [Type] where
  Append '[] l = l
  Append (a ': as) bs = a ': (Append as bs)


happend :: HList ts -> HList ms -> HList (Append ts ms)
happend HNil l = l
happend (HCons a as) l = HCons a (happend as l)




{- EIGHT -}

-- | Type families can also be used to build up constraints. There are, at this
-- point, a couple things that are worth mentioning about constraints:
--
-- - As we saw before, '()' is the empty constraint, which simply has "no
--   effect", and is trivially solved.
--
-- - Unlike tuples, constraints are "auto-flattened": ((a, b), (c, (d, ())) is
--   exactly equivalent to (a, b, c, d). Thanks to this property, we can build
--   up constraints using type families!

type family CAppend (x :: Constraint) (y :: Constraint) :: Constraint where
  CAppend x y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.

type family Every (c :: Type -> Constraint) (x :: [Type]) :: Constraint where
  Every _ '[] = ()
  Every f (t ': ts) = (f t, Every f ts)


-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.

instance Every Show ts => Show (HList ts) where
  show HNil = "HNil"
  show (HCons a as) = "HCons " ++ show a ++ " (" ++ show as ++ ")"

tst = HCons 5 (HCons "sdf" (HCons (1, "qwe") HNil))

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?

instance Every Eq ts => Eq (HList ts) where
  (==) HNil HNil = True
  (==) (HCons a as) (HCons b bs) = a == b && as == bs

instance (Every Eq ts, Every Ord ts) => Ord (HList ts) where
  (<=) HNil HNil = True
  (<=) (HCons a as) (HCons b bs) | a == b = as <= bs
                                 | otherwise = a <= b



{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family CalcNats (n :: Nat) :: [Nat] where
  CalcNats  n =  CalcNats' n '[]

type family CalcNats' (n :: Nat) (acc :: [Nat]) where
  CalcNats' 'Z acc = 'Z ': acc
  CalcNats' ('S n) acc = CalcNats' n (('S n) ': acc)


-- | b. Write a type-level prime number sieve.

-- | c. Why is this such hard work?
