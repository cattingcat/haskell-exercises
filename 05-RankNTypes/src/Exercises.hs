{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE RankNTypes     #-}

{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE ConstraintKinds     #-}


module Exercises where

import Data.Kind (Type, Constraint)





{- ONE -}

-- | The following GADT creates a list of values of unknown types:

data Exlistential where
  Nil  :: Exlistential
  Cons :: a -> Exlistential -> Exlistential

-- | a. Write a function to "unpack" this exlistential into a list.

unpackExlistential :: Exlistential -> (forall a. a -> r) -> [r]
unpackExlistential Nil _ = []
unpackExlistential (Cons a t) f = f a : unpackExlistential t f

-- | b. Regardless of which type @r@ actually is, what can we say about the
-- values in the resulting list?
--
-- forall a . [a]

-- | c. How do we "get back" knowledge about what's in the list? Can we?





{- TWO -}

-- | Consider the following GADT that existentialises a 'Foldable' structure
-- (but, crucially, not the type inside).

data CanFold a where
  CanFold :: Foldable f => f a -> CanFold a

-- | a. The following function unpacks a 'CanFold'. What is its type?
unpackCanFold :: (forall f . Foldable f => f a -> r) -> CanFold a -> r
unpackCanFold f (CanFold x) = f x

-- | b. Can we use 'unpackCanFold' to figure out if a 'CanFold' is "empty"?
-- Could we write @length :: CanFold a -> Int@? If so, write it!
length' :: CanFold a -> Int
length' cf = unpackCanFold length cf

-- | c. Write a 'Foldable' instance for 'CanFold'. Don't overthink it.
instance Foldable CanFold where
  foldMap f (CanFold fl) = foldMap f fl




{- THREE -}

-- | Recall our existential 'EqPair' GADT:

data EqPair where
  EqPair :: Eq a => a -> a -> EqPair

-- | a. Write a function that "unpacks" an 'EqPair' by applying a user-supplied
-- function to its pair of values in the existential type.
unpackEqPair :: (forall a . Eq a => (a, a) -> r) -> EqPair -> r
unpackEqPair f (EqPair a b) = f (a, b)

-- | b. Write a function that takes a list of 'EqPair's and filters it
-- according to some predicate on the unpacked values.
foo :: [EqPair] -> (forall a . Eq a => (a, a) -> Bool) -> [EqPair]
foo l p = filter (unpackEqPair p) l

-- | c. Write a function that unpacks /two/ 'EqPair's. Now that both our
-- variables are in rank-2 position, can we compare values from different
-- pairs?
bar :: EqPair -> EqPair -> (forall a b . (Eq a, Eq b) => (a, a, b, b) -> r) -> r
bar (EqPair a a') (EqPair b b') f = f (a, a', b, b')




{- FOUR -}

-- | When I was building @purescript-panda@, I came across a neat use case for
-- rank-2 types. Consider the following sketch of a type:

data Component input output
  -- = Some sort of component stuff.

-- | Now, let's imagine we want to add a constructor to "nest" a component
-- inside another component type. We need a way of transforming between our
-- "parent" I/O and "child" I/O, so we write this type:

data Nested input output subinput suboutput
  = Nested
      { inner  :: Component subinput suboutput
      , input  :: input -> subinput
      , output :: suboutput -> output
      }

-- | a. Write a GADT to existentialise @subinput@ and @suboutput@.

data NestedX input output where
  NestedX :: (suboutput -> output)
          -> (input     -> subinput)
          -> Component subinput suboutput
          -> NestedX   input    output

-- | b. Write a function to "unpack" a NestedX. The user is going to have to
-- deal with all possible @subinput@ and @suboutput@ types.
unpackNestedX :: NestedX i o -> (forall si so . Component si so -> si-> so) -> i -> o
unpackNestedX (NestedX soO iSi com) f i = soO $ f com (iSi i)

-- | c. Why might we want to existentialise the subtypes away? What do we lose
-- by doing so? What do we gain?

-- In case you're interested in where this actually turned up in the code:
-- https://github.com/i-am-tom/purescript-panda/blob/master/src/Panda/Internal/Types.purs#L84





{- FIVE -}

-- | Let's continue with the theme of the last question. Let's say I have a few
-- HTML-renderable components:

data FirstGo input output
  = FText String
  | FHTML (String, String) [FirstGo input output]
  --       ^ properties     ^ children

-- | This is fine, but there's an issue: some functions only really apply to
-- 'FText' /or/ 'FHTML'. Now that this is a sum type, they'd have to result in
-- a 'Maybe'! Let's avoid this by splitting this sum type into separate types:

data Text = Text String
data HTML = HTML { properties :: (String, String), children :: HtmlChildren }

-- | Uh oh! What's the type of our children? It could be either! In fact, it
-- could probably be anything that implements the following class, allowing us
-- to render our DSL to an HTML string:
class Renderable component where render :: component -> String

-- | a. Write a type for the children.
--data  HtmlChildren = forall a . HtmlChildren (Renderable a => [a])

data  HtmlChildren where
  HtmlChildren :: forall a . Renderable a => [a] -> HtmlChildren

-- | b. What I'd really like to do when rendering is 'fmap' over the children
-- with 'render'; what's stopping me? Fix it!
mapHtmlChildren :: HtmlChildren -> [String]
mapHtmlChildren (HtmlChildren []) = []
mapHtmlChildren (HtmlChildren (c:cs)) = render c : mapHtmlChildren (HtmlChildren cs)

-- | c. Now that we're an established Haskell shop, we would /also/ like the
-- option to render our HTML to a Shakespeare template to write to a file
-- (http://hackage.haskell.org/package/shakespeare). How could we support this
-- new requirement with minimal code changes?





{- SIX -}

-- | Remember our good ol' mystery box?

data MysteryBox a where
  EmptyBox  ::                                MysteryBox ()
  IntBox    :: Int    -> MysteryBox ()     -> MysteryBox Int
  StringBox :: String -> MysteryBox Int    -> MysteryBox String
  BoolBox   :: Bool   -> MysteryBox String -> MysteryBox Bool

-- | a. Knowing what we now know about RankNTypes, we can write an 'unwrap'
-- function! Write the function, and don't be too upset if we need a 'Maybe'.
unpackMysteryBox :: MysteryBox a -> (() -> Maybe Int -> Maybe String -> Maybe Bool -> r) -> r
unpackMysteryBox EmptyBox f = f () Nothing Nothing Nothing
unpackMysteryBox (IntBox i _) f = f () (Just i) Nothing Nothing
unpackMysteryBox (StringBox s (IntBox i _)) f = f () (Just i) (Just s) Nothing
unpackMysteryBox (BoolBox b (StringBox s (IntBox i _))) f = f () (Just i) (Just s) (Just b)

-- | b. Why do we need a 'Maybe'? What can we still not know?

-- | c. Write a function that uses 'unwrap' to print the name of the next
-- layer's constructor.

showMysteryBox :: MysteryBox a -> String
showMysteryBox box = unpackMysteryBox box foo
  where
    foo () Nothing _ _ = "IntBox"
    foo () _ Nothing _ = "StringBox"
    foo () _ _ Nothing = "BoolBox"




{- SEVEN -}

-- | When we talked about @DataKinds@, we briefly looked at the 'SNat' type:

data Nat = Z | S Nat
  deriving (Show, Eq)

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | We also saw that we could convert from an 'SNat' to a 'Nat':

toNat :: SNat n -> Nat
toNat SZ = Z
toNat (SS n) = S (toNat n)

-- | How do we go the other way, though? How do we turn a 'Nat' into an 'SNat'?
-- In the general case, this is impossible: the 'Nat' could be calculated from
-- some user input, so we have no way of knowing what the 'SNat' type would be.
-- However, if we could have a function that would work /for all/ 'SNat'
-- values...
toSNat :: Nat -> (forall (n :: Nat) . Sing n => SNat n -> r) -> r
toSNat Z f = f SZ
toSNat (S n) f = toSNat n (\i -> foo i f)
  where
    foo :: forall (m :: Nat) r . Sing m => SNat m -> (forall (n :: Nat) . Sing n => SNat n -> r) -> r
    foo snat f = f (SS snat)

tst = toSNat (S (S (S Z))) foo
  where
--    foo :: forall (n :: Nat) . ShowNat n => SNat n -> String
    foo (_ :: SNat n) = showNat' (Proxy @n)


data Proxy s = Proxy

showNat' :: forall (n :: Nat) . Sing n => Proxy n -> String
showNat' _ = show (singNat @n)


instance Show (SNat n) where
  show SZ = "z"
  show (SS n) = "s " ++ show n

class Sing (n :: Nat) where
  singNat :: SNat n
instance Sing 'Z where
  singNat = SZ
instance Sing n => Sing ('S n) where
  singNat = SS (singNat @n)

-- | Implement the 'fromNat' function. It should take a 'Nat', along with some
-- SNat-accepting function (maybe at a higher rank?) that returns an @r@, and
-- then returns an @r@. The successor case is a bit weird here - type holes
-- will help you!

-- | If you're looking for a property that you could use to test your function,
-- remember that @fromNat x toNat === x@!


tstNat = S (S (S (S Z)))
tst2 = toSNat tstNat toNat == tstNat



{- EIGHT -}

-- | Bringing our vector type back once again:

data Vector (n :: Nat) (a :: Type) where
  VNil  ::                    Vector  'Z    a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | It would be nice to have a 'filter' function for vectors, but there's a
-- problem: we don't know at compile time what the new length of our vector
-- will be... but has that ever stopped us? Make it so!

filterV :: (a -> Bool) -> Vector n a -> (forall m . Vector m a -> r) -> r
filterV _ VNil f = f VNil
filterV p (VCons a t) f = if p a then foo else filterV p t f
  where
    foo = filterV p t (\v -> bar a v f)

    bar :: a -> Vector m a -> (forall m . Vector m a -> r) -> r
    bar a vect f = f (VCons a vect)

tstVectFilter = filterV (> 3) (VCons 1 (VCons 2 (VCons 3 (VCons 4 (VCons 5 VNil))))) foo
  where
    foo :: Vector _n Int -> String
    foo (VCons a _) = show a
    foo _ = "empty"