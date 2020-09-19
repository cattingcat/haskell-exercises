{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Exercises where

data MyData a where
 Md1 :: String -> MyData String
 Md2 :: Int -> MyData Int
 Md3 :: forall a . Show a => a -> MyData a

foo :: MyData String -> String
foo (Md1 a) = "show a"
foo (Md2 i) = show (i + 666)




{- ONE -}

-- | Let's introduce a new class, 'Countable', and some instances to match.
class Countable a where count :: a -> Int
instance Countable Int  where count   = id
instance Countable [a]  where count   = length
instance Countable Bool where count x = if x then 1 else 0

-- | a. Build a GADT, 'CountableList', that can hold a list of 'Countable'
-- things.

data CountableList where
  L :: Countable a => [a] -> CountableList


-- | b. Write a function that takes the sum of all members of a 'CountableList'
-- once they have been 'count'ed.

countList :: CountableList -> Int
countList (L ls) = foldr (\a i -> i + count a) 0 ls


-- | c. Write a function that removes all elements whose count is 0.

dropZero :: CountableList -> CountableList
dropZero (L ls) = L (filter (\i -> count i /= 0) ls)


-- | d. Can we write a function that removes all the things in the list of type
-- 'Int'? If not, why not?

filterInts :: CountableList -> CountableList
filterInts = error "Contemplate me!"





{- TWO -}

-- | a. Write a list that can take /any/ type, without any constraints.

data AnyList where
  AnyList :: [a] -> AnyList

-- | b. How many of the following functions can we implement for an 'AnyList'?

reverseAnyList :: AnyList -> AnyList
reverseAnyList (AnyList ls) = AnyList (reverse ls)

filterAnyList :: (forall a . a -> Bool) -> AnyList -> AnyList
filterAnyList f (AnyList ls) = AnyList (go ls)
  where
    go (a:as) = if f a then a : go as else go as

lengthAnyList :: AnyList -> Int
lengthAnyList (AnyList ls) = length ls

foldAnyList :: Monoid m => AnyList -> m
foldAnyList _ = mempty

isEmptyAnyList :: AnyList -> Bool
isEmptyAnyList (AnyList []) = True
isEmptyAnyList (AnyList _ ) = False

instance Show AnyList where
  show (AnyList ls) = "AnyList " ++ show (length ls)





{- THREE -}

-- | Consider the following GADT:

data TransformableTo output where
  TransformWith
    :: (input -> output)
    ->  input
    -> TransformableTo output

-- | ... and the following values of this GADT:

transformable1 :: TransformableTo String
transformable1 = TransformWith show 2.5

transformable2 :: TransformableTo String
transformable2 = TransformWith (uncurry (++)) ("Hello,", " world!")

-- | a. Which type variable is existential inside 'TransformableTo'? What is
-- the only thing we can do to it?
-- Ans: input
--      We can call function on it

-- | b. Could we write an 'Eq' instance for 'TransformableTo'? What would we be
-- able to check?
-- Ans: Yes we can. We can compare outputs

-- | c. Could we write a 'Functor' instance for 'TransformableTo'? If so, write
-- it. If not, why not?

instance Functor TransformableTo where
  fmap f (TransformWith trans val) = TransformWith (f . trans) val



{- FOUR -}

-- | Here's another GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. There's one (maybe two) useful function to write for 'EqPair'; what is
-- it?
eq', notEq' :: EqPair -> Bool
eq' (EqPair a b) = a == b
notEq' (EqPair a b) = a /= b


-- | b. How could we change the type so that @a@ is not existential? (Don't
-- overthink it!)
data EqPair' a where
  EqPair' :: Eq a => a -> a -> EqPair' a

-- | c. If we made the change that was suggested in (b), would we still need a
-- GADT? Or could we now represent our type as an ADT?
data EqPair1' a = Eq a => EqPair1' a a




{- FIVE -}

-- | Perhaps a slightly less intuitive feature of GADTs is that we can set our
-- type parameters (in this case @a@) to different types depending on the
-- constructor.

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool


data family MysteryBox' a
data instance MysteryBox' () = EmptyBox'
data instance MysteryBox' Int = IntBox' Int (MysteryBox' ())
data instance MysteryBox' String where
  StringBox' :: MysteryBox' String
  StringBox1' :: MysteryBox' String

-- | When we pattern-match, the type-checker is clever enough to
-- restrict the branches we have to check to the ones that could produce
-- something of the given type.

getInt :: MysteryBox Int -> Int
getInt (IntBox int _) = int

-- | a. Implement the following function by returning a value directly from a
-- pattern-match:

getInt' :: MysteryBox String -> Int
getInt' _doSomeCleverPatternMatching = error "Return that value"

-- | b. Write the following function. Again, don't overthink it!

countLayers :: MysteryBox a -> Int
countLayers EmptyBox = 1
countLayers (IntBox _ _) = 2
countLayers (StringBox _ _) = 3
countLayers (BoolBox _ _) = 4

-- | c. Try to implement a function that removes one layer of "Box". For
-- example, this should turn a BoolBox into a StringBox, and so on. What gets
-- in our way? What would its type be?





{- SIX -}

-- | We can even use our type parameters to keep track of the types inside an
-- 'HList'!  For example, this heterogeneous list contains no existentials:

data HList a where
  HNil  :: HList ()
  HCons :: head -> HList tail -> HList (head, tail)

exampleHList :: HList (String, (Int, (Bool, ())))
exampleHList = HCons "Tom" (HCons 25 (HCons True HNil))

-- | a. Write a 'head' function for this 'HList' type. This head function
-- should be /safe/: you can use the type signature to tell GHC that you won't
-- need to pattern-match on HNil, and therefore the return type shouldn't be
-- wrapped in a 'Maybe'!

-- | b. Currently, the tuples are nested. Can you pattern-match on something of
-- type @HList (Int, String, Bool, ())@? Which constructor would work?

patternMatchMe :: HList (Int, (String, (Bool, ()))) -> Int
patternMatchMe (HCons a _ ) = a

-- | c. Can you write a function that appends one 'HList' to the end of
-- another? What problems do you run into?





{- SEVEN -}

-- | Here are two data types that may help:

data Empty
data Branch left centre right

-- | a. Using these, and the outline for 'HList' above, build a heterogeneous
-- /tree/. None of the variables should be existential.

data HTree a where
  HTNil :: HTree Empty
  HTNode :: HTree l -> a -> HTree r -> HTree (Branch l a r)

-- | b. Implement a function that deletes the left subtree. The type should be
-- strong enough that GHC will do most of the work for you. Once you have it,
-- try breaking the implementation - does it type-check? If not, why not?

rmLeft :: HTree (Branch l a r) -> HTree (Branch Empty a r)
rmLeft (HTNode l a r) = HTNode HTNil a r

-- | c. Implement 'Eq' for 'HTree's. Note that you might have to write more
-- than one to cover all possible HTrees. You might also need an extension or
-- two, so look out for something... flexible... in the error messages!
-- Recursion is your friend here - you shouldn't need to add a constraint to
-- the GADT!

instance Eq (HTree Empty) where
  _ == _ = True

instance (Eq (HTree l), Eq (HTree r), Eq a) => Eq (HTree (Branch l a r)) where
  (HTNode l a r) == (HTNode l' a' r') = l == l' && a == a && r == r'



{- EIGHT -}

-- | a. Implement the following GADT such that values of this type are lists of
-- values alternating between the two types. For example:
--
-- @
--   f :: AlternatingList Bool Int
--   f = ACons True (ACons 1 (ACons False (ACons 2 ANil)))
-- @

data AlternatingList a b where
  ACons :: a -> AlternatingList b a -> AlternatingList a b
  ANil :: AlternatingList a b

-- | b. Implement the following functions.

getFirsts :: AlternatingList a b -> [a]
getFirsts ANil = []
getFirsts (ACons a rest) = a : getSeconds rest

getSeconds :: AlternatingList a b -> [b]
getSeconds ANil = []
getSeconds (ACons _ rest) = getFirsts rest

-- | c. One more for luck: write this one using the above two functions, and
-- then write it such that it only does a single pass over the list.

foldValues :: (Monoid a, Monoid b) => AlternatingList a b -> (a, b)
foldValues ANil = (mempty, mempty)
foldValues (ACons a rest) = let (b', a') = foldValues rest in (a <> a', b')





{- NINE -}

-- | Here's the "classic" example of a GADT, in which we build a simple
-- expression language. Note that we use the type parameter to make sure that
-- our expression is well-formed.

data Expr a where
  Equals    :: Expr Int  -> Expr Int            -> Expr Bool
  Add       :: Expr Int  -> Expr Int            -> Expr Int
  If        :: Expr Bool -> Expr a   -> Expr a  -> Expr a
  IntValue  :: Int                              -> Expr Int
  BoolValue :: Bool                             -> Expr Bool

-- | a. Implement the following function and marvel at the typechecker:

bar :: Expr Bool -> String
bar (Add e1 e2) = ""

eval :: Expr a -> a
eval (Equals le re) = eval le == eval re
eval (Add le re) = eval le + eval re
eval (If b le re) = if eval b then eval le else eval re
eval (IntValue i) = i
eval (BoolValue b) = b

-- | b. Here's an "untyped" expression language. Implement a parser from this
-- into our well-typed language. Note that (until we cover higher-rank
-- polymorphism) we have to fix the return type. Why do you think this is?

data DirtyExpr
  = DirtyEquals    DirtyExpr DirtyExpr
  | DirtyAdd       DirtyExpr DirtyExpr
  | DirtyIf        DirtyExpr DirtyExpr DirtyExpr
  | DirtyIntValue  Int
  | DirtyBoolValue Bool

parse :: DirtyExpr -> Maybe (Expr Int)
parse (DirtyIntValue i) = Just (IntValue i)
parse (DirtyAdd le re) = Add <$> parse le <*> parse re
parse (DirtyIf b le re) = If <$> parseBool b <*> parse le <*> parse re
  where
    parseBool :: DirtyExpr -> Maybe (Expr Bool)
    parseBool (DirtyBoolValue i) = Just (BoolValue i)
    parseBool (DirtyEquals le re) = Equals <$> parse le <*> parse re
    parseBool _ = Nothing
parse _ = Nothing

-- | c. Can we add functions to our 'Expr' language? If not, why not? What
-- other constructs would we need to add? Could we still avoid 'Maybe' in the
-- 'eval' function?





{- TEN -}

-- | Back in the glory days when I wrote JavaScript, I could make a composition
-- list like @pipe([f, g, h, i, j])@, and it would pass a value from the left
-- side of the list to the right. In Haskell, I can't do that, because the
-- functions all have to have the same type :(

-- | a. Fix that for me - write a list that allows me to hold any functions as
-- long as the input of one lines up with the output of the next.

data TypeAlignedList a b where
  TALEmpty :: TypeAlignedList a a
  TALCons :: (a -> a') -> TypeAlignedList a' b -> TypeAlignedList a b

-- | b. Which types are existential?

-- | c. Write a function to append type-aligned lists. This is almost certainly
-- not as difficult as you'd initially think.

composeTALs :: TypeAlignedList b c -> TypeAlignedList a b -> TypeAlignedList a c
composeTALs TALEmpty TALEmpty = TALEmpty
composeTALs TALEmpty a = a
composeTALs a TALEmpty = a
composeTALs m (TALCons f l) = TALCons f (composeTALs m l)
