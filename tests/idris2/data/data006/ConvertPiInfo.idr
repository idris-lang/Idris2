--------------
-- Explicit --
--------------

data EI : Type -> Type
data EI : {_ : Type} -> Type where

data EA : Type -> Type
data EA : {auto _ : Type} -> Type where

data ED : Type -> Type
data ED : {default Int _ : Type} -> Type where

--------------
-- Implicit --
--------------

data IE : {_ : Type} -> Type
data IE : Type -> Type where

data IA : {_ : Type} -> Type
data IA : {auto _ : Type} -> Type where

data ID : {_ : Type} -> Type
data ID : {default Int _ : Type} -> Type where

----------
-- Auto --
----------

data AE : {auto _ : Type} -> Type
data AE : Type -> Type where

data AI : {auto _ : Type} -> Type
data AI : {_ : Type} -> Type where

data AD : {auto _ : Type} -> Type
data AD : {default Int _ : Type} -> Type where

-------------
-- Default --
-------------

data DE : {default Int _ : Type} -> Type
data DE : Type -> Type where

data DI : {default Int _ : Type} -> Type
data DI : {_ : Type} -> Type where

data DA : {default Int _ : Type} -> Type
data DA : {auto _ : Type} -> Type where
