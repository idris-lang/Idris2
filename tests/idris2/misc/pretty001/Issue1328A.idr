module Issue1328A
%default total

infix 4 `InCtx`
data InCtx : (a, b : Type) -> Type where

prop0 : a `InCtx` b
prop0 = ?undef_0

prop1 : (`InCtx` b) a
prop1 = ?undef_1

prop2 : (a `InCtx`) b
prop2 = ?undef_2

def0 : (m, n : Integer) -> Integer
def0 m n = m `div` n

def1 : (m, n : Integer) -> Integer
def1 m n = (`div` n) m

def2 : (m, n : Integer) -> Integer
def2 m n = (m `div`) n

infix 4 |-
data (|-) : (a, b : Type) -> Type where

inProp0 : a |- b
inProp0 = ?undef_3

inProp1 : (|- b) a
inProp1 = ?undef_4

inProp2 : (a |-) b
inProp2 = ?undef_5

inDef0 : Nat
inDef0 = 42 + 21

inDef1 : Nat
inDef1 = (+ 21) 42

inDef2 : Nat
inDef2 = (42 +) 21
