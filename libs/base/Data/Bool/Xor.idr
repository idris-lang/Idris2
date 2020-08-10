module Data.Bool.Xor

import Data.Bool

%default total

public export
xor : Bool -> Bool -> Bool
xor True True = False
xor False False = False
xor _ _ = True

export
xorSameFalse : (b : Bool) -> xor b b = False
xorSameFalse False = Refl
xorSameFalse True = Refl

export
xorFalseNeutral : (b : Bool) -> xor False b = b
xorFalseNeutral False = Refl
xorFalseNeutral True = Refl

export
xorTrueNot : (b : Bool) -> xor True b = not b
xorTrueNot False = Refl
xorTrueNot True  = Refl

export
notXor : (a, b : Bool) -> not (xor a b) = xor (not a) b
notXor True  b = rewrite xorFalseNeutral b in
                 rewrite xorTrueNot b in
                 notInvolutive b
notXor False b = rewrite xorFalseNeutral b in
                 sym $ xorTrueNot b

export
notXorCancel : (a, b : Bool) -> xor (not a) (not b) = xor a b
notXorCancel True  b = rewrite xorFalseNeutral (not b) in
                       sym $ xorTrueNot b
notXorCancel False b = rewrite xorFalseNeutral b in
                       rewrite xorTrueNot (not b) in
                       notInvolutive b

export
xorAssociative : (a, b, c : Bool) -> xor a (xor b c) = xor (xor a b) c
xorAssociative False b c =
  rewrite xorFalseNeutral b in
  xorFalseNeutral $ xor b c
xorAssociative True  b c =
  rewrite xorTrueNot b in
  rewrite xorTrueNot (xor b c) in
  notXor b c

export
xorCommutative : (a, b : Bool) -> xor a b = xor b a
xorCommutative False False = Refl
xorCommutative False True  = Refl
xorCommutative True  False = Refl
xorCommutative True  True  = Refl

export
xorNotTrue : (a : Bool) -> a `xor` (not a) = True
xorNotTrue False = Refl
xorNotTrue True  = Refl
