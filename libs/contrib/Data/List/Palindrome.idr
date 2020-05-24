module Data.List.Palindrome

import Data.List.Views
import Data.List.Reverse

||| Do geese see God?
public export
data Palindrome : (xs : List a) -> Type where
  Empty  : Palindrome []
  Single : Palindrome [_]
  Multi  : Palindrome xs -> Palindrome $ x :: (xs ++ [x])

||| A Palindrome reversed is itself.
export
palindromeReverse : (xs : List a) -> Palindrome xs -> reverse xs = xs
palindromeReverse [] Empty = Refl
palindromeReverse [_] Single = Refl
palindromeReverse ([x] ++ ys ++ [x]) (Multi pf) =
  rewrite reverseAppend ([x] ++ ys) [x] in
    rewrite reverseAppend [x] ys in
      rewrite palindromeReverse ys pf in
        Refl

private
reversePalindromeEqualsLemma
  : (x, x' : a)
  -> (xs : List a)
  -> reverse (x :: (xs ++ [x'])) = (x :: (xs ++ [x']))
  -> (reverse xs = xs, x = x')
reversePalindromeEqualsLemma x x' xs prf = equateInnerAndOuter (flipHeadX prf)
  where
    flipHeadX : reverse (x :: (xs ++ [x'])) = x :: (xs ++ [x']) -> reverse (xs ++ [x']) ++ [x] = x :: (xs ++ [x'])
    flipHeadX prf = rewrite (sym (reverseCons x (xs ++ [x']))) in prf
    flipLastX' : reverse (xs ++ [x']) = x :: xs -> (x' :: reverse xs) = (x :: xs)
    flipLastX' prf = rewrite (sym $ reverseAppend xs [x']) in prf
    cancelOuter : (reverse (xs ++ [x'])) = x :: xs -> reverse xs = xs
    cancelOuter prf = snd (consInjective (flipLastX' prf))
    equateInnerAndOuter : reverse (xs ++ [x']) ++ [x] = (x :: xs) ++ [x'] -> (reverse xs = xs, x = x')
    equateInnerAndOuter prf =
      let (prf', xEqualsX') = unfoldEqualSnoc x x' (reverse (xs ++ [x'])) (x :: xs) prf
       in (cancelOuter prf', xEqualsX')

||| Only Palindromes are equal to their own reverse.
reversePalindrome : (xs : List a) -> reverse xs = xs -> Palindrome xs
reversePalindrome [] _ = Empty
reversePalindrome (x :: []) _ = Single
reversePalindrome (x :: xs) prf with (snocList xs)
  reversePalindrome (x :: (xs ++ [x'])) prf | Snoc x' xs _ with (reversePalindromeEqualsLemma x x' xs prf)
    reversePalindrome (x :: (xs ++ [x])) prf | Snoc x xs _ | (revXsIsIdentical, Refl) =
      Multi (reversePalindrome xs revXsIsIdentical)
