module Issue

%default total

data Layer : Type where
  MkAsk : (kprf : Layer) -> Layer

data View : Layer -> Type where
  AView : (0 kprf : Layer) -> View (MkAsk kprf)

view1 : (0 target2 : Layer) -> View target2
view1 (MkAsk mkk) = AView mkk

f1 : (0 target2 : Layer) -> ()
f1 target2 = case view1 target2 of
  AView avk => f1 avk
