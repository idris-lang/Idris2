module Data.Linear.LMaybe

import Data.Linear.Bifunctor
import Data.Linear.Interface
import Data.Linear.Notation

%default total

||| Linear version of Maybe
public export
data LMaybe : Type -> Type where
  Nothing : LMaybe a
  Just : a -@ LMaybe a

export
(<$>) : (a -@ b) -> LMaybe a -@ LMaybe b
f <$> Nothing = Nothing
f <$> Just x = Just (f x)

export
Consumable a => Consumable (LMaybe a) where
  consume Nothing = ()
  consume (Just a) = consume a

export
Duplicable a => Duplicable (LMaybe a) where
  duplicate Nothing = [Nothing, Nothing]
  duplicate (Just a) = Just <$> duplicate a
