import Data.SnocList

A, B, C, D, E : SnocList Nat
A = [<]

B = Lin :< 1 :< 2 :< 3

C = [< 1, 2, 3]

D = [< 1, 2, 3] :< 4

E = [< 1, 2, 3] <>< [4, 5, 6]

X : List Nat
X = [< 1, 2, 3] <>> [> 4, 5, 6]

StaticTest1 : B = C
StaticTest1 = Refl

StaticTest2 : E <>> [] = X
StaticTest2 = Refl

DynamicTest1  ,
DynamicTest2 : Bool
DynamicTest1 = B == C
DynamicTest2 = (E <>> []) == X

S1,S2,S3 : String
S1 = show A
S2 = show B
S3 = show C
