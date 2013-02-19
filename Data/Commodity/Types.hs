{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}

module Data.Commodity.Types where

import Control.Applicative
import Control.Comonad.Trans.Store
import Control.DeepSeq
import Control.Lens
import Control.Monad (join)
import Data.Data
import Data.Distributive
import Data.Foldable as Foldable
import Data.Functor.Bind as Bind
import Data.Functor.Representable as Repr
import Data.IntMap as IntMap
import Data.Key
import Data.Monoid
import Data.Traversable as Traversable
import Linear.Vector

nullCommodity = 0

type CommodityIdx = IntMap.Key

data Balance a = Zero
               | Amount CommodityIdx a
               | Balance (IntMap (Balance a))
               deriving (Typeable, Data)

instance Eq (Balance a)
instance Show (Balance a)
instance Read (Balance a)

instance Additive Balance where
    zero = Zero

    Zero ^+^ x    = x
    x    ^+^ Zero = x

    x@(Amount cx qx) ^+^ y@(Amount cy qy)
        | cx /= cy   = Balance (fromList [(cx,x), (cy,y)])
        | otherwise = Amount cx (qx + qy)

    x@(Amount cx _) ^+^ Balance ys =
        Balance (ys & at cx.non Zero %~ (^+^ x))
    Balance xs ^+^ y@(Amount cy _) =
        Balance (xs & at cy.non Zero %~ (^+^ y))

    x@(Balance _) ^+^ Balance ys = Balance (fmap (x ^+^) ys)
    {-# INLINE (^+^) #-}

    Zero ^-^ Zero       = Zero
    Zero ^-^ Amount c q = Amount c (-q)
    Zero ^-^ Balance ys = Balance (fmap (Zero ^-^) ys)
    x    ^-^ Zero       = x

    x@(Amount cx qx) ^-^ y@(Amount cy qy)
        | cx /= cy   = Balance (fromList [(cx,x), (cy,Zero ^-^ y)])
        | otherwise = Amount cx (qx - qy)

    x@(Amount cx qx) ^-^ Balance ys =
        Balance (fmap (Zero ^-^) ys & at cx.non Zero %~ (^+^ x))
    Balance xs ^-^ y@(Amount cy qy) =
        Balance (xs & at cy.non Zero %~ (^-^ y))

    x@(Balance _) ^-^ Balance ys = Balance (fmap (x ^-^) ys)
    {-# INLINE (^-^) #-}

instance Functor Balance where
    fmap f Zero         = Zero
    fmap f (Amount c x) = Amount c (f x)
    fmap f (Balance xs) = Balance (fmap (fmap f) xs)

instance Applicative Balance where
    pure x = Amount nullCommodity x

    Zero <*> _ = Zero

    Amount _ _ <*> Zero         = Zero
    Amount _ f <*> Amount cy qy = Amount cy (f qy)
    Amount _ f <*> Balance xs   = Balance (fmap (fmap f) xs)

    Balance fs <*> Zero           = Zero
    Balance fs <*> y@(Amount _ _) = Balance (fmap (<*> y) fs)
    Balance fs <*> Balance ys     =
        Balance $ fmap (\y -> Balance (fmap (<*> y) fs)) ys

instance Apply Balance where
    (<.>) = (<*>)

instance Bind Balance where
    Zero >>- _       = Zero
    Amount _ q >>- f = f q
    Balance xs >>- f = Balance (fmap (>>- f) xs)

instance Monad Balance where
    return = pure
    (>>=) = (>>-)

type instance Data.Key.Key Balance = IntMap.Key

instance Lookup Balance where
    lookup k Zero = Nothing
    lookup k (Amount c x) = if k == c then Just x else Nothing
    lookup k (Balance xs) = case IntMap.lookup k xs of
        Nothing -> Nothing
        Just x  -> Data.Key.lookup k x

instance Data.Key.Indexable Balance where
    index Zero k = error "Key not in zero Balance"
    index (Amount c x) k = if c == k
                           then x
                           else error "Key not in zero Balance"
    index (Balance xs) k = index (index xs k) k

-- type instance Data.Key.Key IntMap = IntMap.Key

-- instance Repr.Representable IntMap where
--     tabulate f = IntMap.fromList (Prelude.map (\x -> (x,f x)) [0..])

-- instance Repr.Representable Balance where
--     tabulate f = Balance (tabulate (\k -> Amount k (f k)))

-- instance At Int Balance where
--   at k = indexed $ \f m ->
--     let mv = Data.Key.lookup k m
--         go Nothing   = maybe m (const (IntMap.delete k m)) mv
--         go (Just v') = IntMap.insert k v' m
--     in go <$> f k mv where
--   {-# INLINE at #-}
--   _at k = indexed $ \f m -> case IntMap.lookup k m of
--      Just v -> f k v <&> \v' -> IntMap.insert k v' m
--      Nothing -> pure m
--   {-# INLINE _at #-}

-- instance Adjustable Balance where
--     adjust f k x = x & at k.mapped %~ f

-- instance Store Balance where
--     extract (Amount _ x) = x
--     extract (Amount _ x) = x
--     (>>=) = (>>-)

instance Foldable Balance where
    foldMap f Zero         = mempty
    foldMap f (Amount _ x) = f x
    foldMap f (Balance xs) = foldMap (foldMap f) xs

    foldr f z Zero         = z
    foldr f z (Amount _ x) = f x z
    foldr f z (Balance xs) = Foldable.foldr (flip (Foldable.foldr f)) z xs

instance Traversable Balance where
    traverse f Zero         = pure Zero
    traverse f (Amount c x) = fmap (Amount c) (f x)
    traverse f (Balance xs) = fmap Balance (traverse (traverse f) xs)

    sequenceA Zero         = pure Zero
    sequenceA (Amount c x) = fmap (Amount c) x
    sequenceA (Balance xs) = fmap Balance (traverse sequenceA xs)

instance Num a => Monoid (Balance a) where
    mempty = Zero

    mappend Zero x = x
    mappend y Zero = y

    mappend x@(Amount cx qx) y@(Amount cy qy)
        | cx /= cy   = Balance (IntMap.fromList [(cx,x),(cy,y)])
        | otherwise = Amount cx (qx + qy)

    mappend x@(Amount cx _) y@(Balance ys) =
        Balance (IntMap.singleton cx x <> ys)
    mappend x@(Balance xs) y@(Amount cy _) =
        Balance (xs <> IntMap.singleton cy y)

    mappend (Balance xs) (Balance ys) = Balance (xs <> ys)

class Monoid g => Group g where
    inverse :: g -> g

instance Num a => Group (Balance a) where
    inverse x = Zero ^-^ x

instance (NFData a) => NFData (Balance a) where
    rnf Zero         = ()
    rnf (Amount c q) = rnf c `seq` rnf q `seq` ()
    rnf (Balance bs) = rnf bs `seq` ()

balanceStore k x = store (index x) k

sum :: Num a => [Balance a] -> Balance a
sum = Foldable.foldr (^+^) Zero
