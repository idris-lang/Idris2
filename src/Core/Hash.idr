module Core.Hash

import Core.CaseTree
import Core.TT

import Data.List
import Data.List1
import Data.Strings

%default covering

-- This is so that we can store a hash of the interface in ttc files, to avoid
-- the need for reloading modules when no interfaces have changed in imports.
-- As you can probably tell, I know almost nothing about writing good hash
-- functions, so better implementations will be very welcome...

public export
interface Hashable a where
  hash : a -> Int
  hashWithSalt : Int -> a -> Int

  hash = hashWithSalt 5381
  hashWithSalt h i = h * 33 + hash i

infixl 5 `hashWithSalt`

export
Hashable Int where
  hash = id

export
Hashable Integer where
  hash = fromInteger

export
Hashable Nat where
  hash = cast

export
Hashable Char where
  hash = cast

export
Hashable a => Hashable (List a) where
  hashWithSalt h [] = abs h
  hashWithSalt h (x :: xs) = hashWithSalt (h * 33 + hash x) xs

export
Hashable a => Hashable (List1 a) where
  hashWithSalt h (x ::: xs) = hashWithSalt (h * 33 + hash x) xs

export
Hashable a => Hashable (Maybe a) where
  hashWithSalt h Nothing = abs h
  hashWithSalt h (Just x) = hashWithSalt h x

export
Hashable String where
  hashWithSalt h str = hashChars h 0 (cast (length str)) str
    where
      hashChars : Int -> Int -> Int -> String -> Int
      hashChars h p len str
          = assert_total $
              if p == len
                 then h
                 else hashChars (h * 33 + cast (strIndex str p))
                                (p + 1) len str

export
Hashable Namespace where
  hashWithSalt h ns = hashWithSalt h (unsafeUnfoldNamespace ns)

export
Hashable Name where
  hashWithSalt h (MN s _) = hashWithSalt h s
  hashWithSalt h (DN _ n) = hashWithSalt h n
  hashWithSalt h (NS ns n) = hashWithSalt (hashWithSalt h ns) n
  hashWithSalt h (Resolved i) = hashWithSalt h i
  hashWithSalt h n = hashWithSalt h (show n)

export
Hashable RigCount where
  hashWithSalt h = elimSemi
                     (hashWithSalt h 0)
                     (hashWithSalt h 1)
                     (const $ hashWithSalt h 2)

export
Hashable t => Hashable (PiInfo t) where
  hashWithSalt h Implicit = hashWithSalt h 0
  hashWithSalt h Explicit = hashWithSalt h 1
  hashWithSalt h AutoImplicit = hashWithSalt h 2
  hashWithSalt h (DefImplicit t) = h `hashWithSalt` 3 `hashWithSalt` t

export
Hashable ty => Hashable (Binder ty) where
  hashWithSalt h (Lam _ c p ty)
      = h `hashWithSalt` 0 `hashWithSalt` c `hashWithSalt` p `hashWithSalt` ty
  hashWithSalt h (Let _ c val ty)
      = h `hashWithSalt` 1 `hashWithSalt` c `hashWithSalt` val `hashWithSalt` ty
  hashWithSalt h (Pi _ c p ty)
      = h `hashWithSalt` 2 `hashWithSalt` c `hashWithSalt` p `hashWithSalt` ty
  hashWithSalt h (PVar _ c p ty)
      = h `hashWithSalt` 3 `hashWithSalt` c `hashWithSalt` p `hashWithSalt` ty
  hashWithSalt h (PLet _ c val ty)
      = h `hashWithSalt` 4 `hashWithSalt` c `hashWithSalt` val `hashWithSalt` ty
  hashWithSalt h (PVTy _ c ty)
      = h `hashWithSalt` 5 `hashWithSalt` c `hashWithSalt` ty

Hashable (Var vars) where
  hashWithSalt h (MkVar {i} _) = hashWithSalt h i

mutual
  export
  Hashable (Term vars) where
    hashWithSalt h (Local fc x idx y)
        = h `hashWithSalt` 0 `hashWithSalt` idx
    hashWithSalt h (Ref fc x name)
        = h `hashWithSalt` 1 `hashWithSalt` name
    hashWithSalt h (Meta fc x y xs)
        = h `hashWithSalt` 2 `hashWithSalt` y `hashWithSalt` xs
    hashWithSalt h (Bind fc x b scope)
        = h `hashWithSalt` 3 `hashWithSalt` b `hashWithSalt` scope
    hashWithSalt h (App fc fn arg)
        = h `hashWithSalt` 4 `hashWithSalt` fn `hashWithSalt` arg
    hashWithSalt h (As fc _ nm pat)
        = h `hashWithSalt` 5 `hashWithSalt` nm `hashWithSalt` pat
    hashWithSalt h (TDelayed fc x y)
        = h `hashWithSalt` 6 `hashWithSalt` y
    hashWithSalt h (TDelay fc x t y)
        = h `hashWithSalt` 7 `hashWithSalt` t `hashWithSalt` y
    hashWithSalt h (TForce fc r x)
        = h `hashWithSalt` 8 `hashWithSalt` x
    hashWithSalt h (PrimVal fc c)
        = h `hashWithSalt` 9 `hashWithSalt` (show c)
    hashWithSalt h (Erased fc _)
        = hashWithSalt h 10
    hashWithSalt h (TType fc)
        = hashWithSalt h 11

  export
  Hashable Pat where
    hashWithSalt h (PAs fc nm pat)
        = h `hashWithSalt` 0 `hashWithSalt` nm `hashWithSalt` pat
    hashWithSalt h (PCon fc x tag arity xs)
        = h `hashWithSalt` 1 `hashWithSalt` x `hashWithSalt` xs
    hashWithSalt h (PTyCon fc x arity xs)
        = h `hashWithSalt` 2 `hashWithSalt` x `hashWithSalt` xs
    hashWithSalt h (PConst fc c)
        = h `hashWithSalt` 3 `hashWithSalt` (show c)
    hashWithSalt h (PArrow fc x s t)
        = h `hashWithSalt` 4 `hashWithSalt` s `hashWithSalt` t
    hashWithSalt h (PDelay fc r t p)
        = h `hashWithSalt` 5 `hashWithSalt` t `hashWithSalt` p
    hashWithSalt h (PLoc fc x)
        = h `hashWithSalt` 6 `hashWithSalt` x
    hashWithSalt h (PUnmatchable fc x)
        = h `hashWithSalt` 7 `hashWithSalt` x

  export
  Hashable (CaseTree vars) where
    hashWithSalt h (Case idx x scTy xs)
        = h `hashWithSalt` 0 `hashWithSalt` idx `hashWithSalt` xs
    hashWithSalt h (STerm _ x)
        = h `hashWithSalt` 1 `hashWithSalt` x
    hashWithSalt h (Unmatched msg)
        = h `hashWithSalt` 2
    hashWithSalt h Impossible
        = h `hashWithSalt` 3

  export
  Hashable (CaseAlt vars) where
    hashWithSalt h (ConCase x tag args y)
        = h `hashWithSalt` 0 `hashWithSalt` x `hashWithSalt` args
            `hashWithSalt` y
    hashWithSalt h (DelayCase t x y)
        = h `hashWithSalt` 2 `hashWithSalt` (show t)
            `hashWithSalt` (show x) `hashWithSalt` y
    hashWithSalt h (ConstCase x y)
        = h `hashWithSalt` 3 `hashWithSalt` (show x) `hashWithSalt` y
    hashWithSalt h (DefaultCase x)
        = h `hashWithSalt` 4 `hashWithSalt` x
