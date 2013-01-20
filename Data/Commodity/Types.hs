{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Linear.Sparse
-- Copyright   :  (C) 2013 John Wiegley,
--                (C) 2012-2013 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  John Wiegley <johnw@fpcomplete.com>,
--                Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Representation and operations on sparse vector spaces and matrices
----------------------------------------------------------------------------
module Data.Commodity.Types where

import Control.Applicative
import Control.DeepSeq
import Control.Lens
import Control.Monad (join)
import Data.Data
import Data.Distributive
import Data.Foldable as Foldable
import Data.Functor.Bind as Bind
import Data.IntMap as IntMap
import Data.Monoid
import Data.Traversable as Traversable
import Linear.Vector

nullCommodity = 0

data Balance a = Zero
               | Amount Int a
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
    x@(Balance xs) ^+^ y@(Amount cy _) =
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

    x@(Amount cx qx) ^-^ y@(Balance ys) =
        Balance (fmap (Zero ^-^) ys & at cx.non Zero %~ (^+^ x))
    x@(Balance xs) ^-^ y@(Amount cy qy) =
        Balance (xs & at cy.non Zero %~ (^-^ y))

    x@(Balance _) ^-^ Balance ys = Balance (fmap (x ^-^) ys)
    {-# INLINE (^-^) #-}

instance Functor Balance where
    fmap f Zero         = Zero
    fmap f (Amount i a) = Amount i (f a)
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

instance Additive Balance => Bind Balance where
    join Zero = Zero

    join (Amount c Zero)           = Zero
    join (Amount _ x@(Amount _ _)) = x
    join (Amount _ x@(Balance _))  = x

    join x@(Balance xs) = Foldable.foldr (^+^) Zero x

instance Foldable Balance where
    foldMap f Zero         = mempty
    foldMap f (Amount i a) = f a
    foldMap f (Balance xs) = foldMap (foldMap f) xs

    foldr f x Zero         = x
    foldr f x (Amount i a) = f a x
    foldr f x (Balance xs) = Foldable.foldr (flip (Foldable.foldr f)) x xs

instance Traversable Balance where
    traverse f Zero         = pure Zero
    traverse f (Amount i a) = fmap (Amount i) (f a)
    traverse f (Balance xs) = fmap Balance (traverse (traverse f) xs)

    sequenceA Zero         = pure Zero
    sequenceA (Amount i a) = fmap (Amount i) a
    sequenceA (Balance xs) = fmap Balance (traverse sequenceA xs)

instance Num a => Monoid (Balance a) where
    mempty = Zero

    mappend Zero x = x
    mappend y Zero = y

    mappend x@(Amount cx qx) y@(Amount cy qy)
        | cx /= cy   = Balance (IntMap.fromList [(cx,x),(cy,y)])
        | otherwise = Amount cx (qx + qy)

    mappend x@(Amount cx _) y@(Balance ys) =
        Balance (IntMap.fromList [(cx,x)] <> ys)
    mappend x@(Balance xs) y@(Amount cy _) =
        Balance (xs <> IntMap.fromList [(cy,y)])

    mappend (Balance xs) (Balance ys) = Balance (xs <> ys)

class Monoid g => Group g where
    inverse :: g -> g

instance Num a => Group (Balance a) where
    inverse x = Zero ^-^ x

instance (NFData a) => NFData (Balance a) where
    rnf Zero         = ()
    rnf (Amount c q) = rnf c `seq` rnf q `seq` ()
    rnf (Balance bs) = rnf bs `seq` ()

sum :: Num a => [Balance a] -> Balance a
sum = Foldable.foldr (^+^) Zero