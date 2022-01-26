module Libraries.Text.Bounded

%default total


public export
record Bounds where
  constructor MkBounds
  ||| 0-based first line
  startLine : Int
  ||| 0-based first col
  startCol : Int
  ||| 0-based last line of bound
  endLine : Int
  ||| 0-based first column after bound
  endCol : Int

Show Bounds where
  showPrec d (MkBounds sl sc el ec) =
    showCon d "MkBounds" (concat [showArg sl, showArg sc, showArg el, showArg ec])

export
startBounds : Bounds -> (Int, Int)
startBounds b = (b.startLine, b.startCol)

export
endBounds : Bounds -> (Int, Int)
endBounds b = (b.endLine, b.endCol)

export
Eq Bounds where
  (MkBounds sl sc el ec) == (MkBounds sl' sc' el' ec') =
      sl == sl'
   && sc == sc'
   && el == el'
   && ec == ec'

public export
record WithBounds ty where
  constructor MkBounded
  val : ty
  isIrrelevant : Bool
  bounds : Bounds

export
start : WithBounds ty -> (Int, Int)
start = startBounds . bounds

export
end : WithBounds ty -> (Int, Int)
end = endBounds . bounds

export
Eq ty => Eq (WithBounds ty) where
  (MkBounded val ir bd) == (MkBounded val' ir' bd') =
    val == val' && ir == ir' && bd == bd'

export
Show ty => Show (WithBounds ty) where
  showPrec d (MkBounded val ir bd) =
    showCon d "MkBounded" (concat [showArg ir, showArg val, showArg bd])

export
Functor WithBounds where
  map f (MkBounded val ir bd) = MkBounded (f val) ir bd

export
Foldable WithBounds where
  foldr c n b = c b.val n

export
Traversable WithBounds where
  traverse f (MkBounded v a bd) = (\ v => MkBounded v a bd) <$> f v

export
irrelevantBounds : ty -> WithBounds ty
irrelevantBounds x = MkBounded x True (MkBounds (-1) (-1) (-1) (-1))

export
removeIrrelevance : WithBounds ty -> WithBounds ty
removeIrrelevance (MkBounded val ir bd) = MkBounded val True bd

export
mergeBounds : WithBounds ty -> WithBounds ty' -> WithBounds ty'
mergeBounds (MkBounded _ True _) (MkBounded val True _) = irrelevantBounds val
mergeBounds (MkBounded _ True _) b2 = b2
mergeBounds b1 (MkBounded val True _) = const val <$> b1
mergeBounds b1 b2 =
  let (ur, uc) = min (start b1) (start b2)
      (lr, lc) = max (end b1) (end b2) in
      MkBounded b2.val False (MkBounds ur uc lr lc)

export
joinBounds : WithBounds (WithBounds ty) -> WithBounds ty
joinBounds b = mergeBounds b b.val
