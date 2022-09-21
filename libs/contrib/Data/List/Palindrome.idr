module Data.List.Palindrome

import Data.List
import Data.List.Views.Extra
import Data.List.Reverse
import Data.List.Equalities

%hide Prelude.reverse
%default total

||| Do geese see God?
public export
data Palindrome : (xs : List a) -> Type where
  Empty  : Palindrome []
  Single : Palindrome [_]
  Multi  : Palindrome xs -> Palindrome (x :: (xs `snoc` x))

||| A Palindrome reversed is itself.
export
palindromeReverse : (xs : List a) -> Palindrome xs -> reverse xs = xs
palindromeReverse [] Empty = Refl
palindromeReverse [_] Single = Refl
palindromeReverse ([x] ++ ys ++ [x]) (Multi pf) =
  rewrite sym $ revAppend ([x] ++ ys) [x] in
    rewrite sym $ revAppend [x] ys in
      rewrite palindromeReverse ys pf in
        Refl

private
reversePalindromeEqualsLemma
  : (x, x' : a)
  -> (xs : List a)
  -> reverse (x :: (xs ++ [x'])) = (x :: (xs ++ [x']))
  -> (reverse xs = xs, x = x')
reversePalindromeEqualsLemma x x' xs prf = equateInnerAndOuter flipHeadX
  where
    flipHeadX : reverse (xs ++ [x']) ++ [x] = x :: (xs ++ [x'])
    flipHeadX = rewrite (sym (reverseCons x (xs ++ [x']))) in prf
    flipLastX' : reverse (xs ++ [x']) = x :: xs -> (x' :: reverse xs) = (x :: xs)
    flipLastX' prf = rewrite (revAppend xs [x']) in prf
    cancelOuter : (reverse (xs ++ [x'])) = x :: xs -> reverse xs = xs
    cancelOuter prf = snd (biinjective (flipLastX' prf))
    equateInnerAndOuter
      : reverse (xs ++ [x']) ++ [x] = (x :: xs) ++ [x']
      -> (reverse xs = xs, x = x')
    equateInnerAndOuter prf =
      let (prf', xEqualsX') = snocInjective prf
       in (cancelOuter prf', xEqualsX')

||| Only Palindromes are equal to their own reverse.
export
reversePalindrome : (xs : List a) -> reverse xs = xs -> Palindrome xs
reversePalindrome input prf with (vList input)
  reversePalindrome [] _ | VNil = Empty
  reversePalindrome [x] _ | VOne = Single
  reversePalindrome (x :: (inner `snoc` y)) prf | VCons rec with (reversePalindromeEqualsLemma x y inner prf)
    reversePalindrome (x :: (inner `snoc` y)) prf | VCons rec | (revInnerIsIdentical, xIsY) =
      rewrite xIsY in
        Multi $ reversePalindrome inner revInnerIsIdentical | Force rec
