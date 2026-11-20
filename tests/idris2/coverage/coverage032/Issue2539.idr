import Data.List.Elem

%default total

mapMaybeList : (s -> s') -> List (Maybe s) -> List (Maybe s')
mapMaybeList f xs = map (map f) xs

mapMaybeListSpec : (xs : List (Maybe s))
              -> (f : s -> s')
              -> (e : Maybe s)
              -> map f e `Elem` (mapMaybeList f xs)
              -> e `Elem` xs
mapMaybeListSpec [] f e pos = absurd pos
mapMaybeListSpec (Nothing :: xs) f Nothing Here = Here
mapMaybeListSpec (_ :: xs) f Nothing (There pos) = There (mapMaybeListSpec xs f Nothing pos)
mapMaybeListSpec (_ :: xs) f (Just z) (There pos) = There (mapMaybeListSpec xs f (Just z) pos)
