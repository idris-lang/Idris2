module Text.Bounded

%default total

public export
record WithBounds ty where
  constructor MkBounded
  val : ty
  isIrrelevant : Bool
  startLine : Int
  startCol : Int
  endLine : Int
  endCol : Int

export
start : WithBounds ty -> (Int, Int)
start b = (b.startLine, b.startCol)

export
end : WithBounds ty -> (Int, Int)
end b = (b.endLine, b.endCol)

export
Eq ty => Eq (WithBounds ty) where
  (MkBounded val ir sl sc el ec) == (MkBounded val' ir' sl' sc' el' ec') =
    val == val' && ir == ir' && sl == sl' && sc == sc' && el == el' && ec == ec'

export
Show ty => Show (WithBounds ty) where
  showPrec d (MkBounded val ir sl sc el ec) =
    showCon d "MkBounded" (concat [showArg ir, showArg val, showArg sl, showArg sc, showArg el, showArg ec])

export
Functor WithBounds where
  map f (MkBounded val ir sl sc el ec) = MkBounded (f val) ir sl sc el ec

export
Foldable WithBounds where
  foldr c n b = c b.val n

export
Traversable WithBounds where
  traverse f (MkBounded v a b c d e) = (\ v => MkBounded v a b c d e) <$> f v

export
irrelevantBounds : ty -> WithBounds ty
irrelevantBounds x = MkBounded x True (-1) (-1) (-1) (-1)

export
mergeBounds : WithBounds ty -> WithBounds ty' -> WithBounds ty'
mergeBounds (MkBounded _ True _ _ _ _) (MkBounded val True _ _ _ _) = irrelevantBounds val
mergeBounds (MkBounded _ True _ _ _ _) b2 = b2
mergeBounds b1 (MkBounded val True _ _ _ _) = const val <$> b1
mergeBounds b1 b2 =
  let (ur, uc) = min (start b1) (start b2)
      (lr, lc) = max (end b1) (end b2) in
      MkBounded b2.val False ur uc lr lc

export
joinBounds : WithBounds (WithBounds ty) -> WithBounds ty
joinBounds b = mergeBounds b b.val
