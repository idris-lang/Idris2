namespace Hoo

  f : Either a b -> Either b a
  f (Left a) = Right a
  f (Right b) = Left b

  natural : (xs : Either a b) -> ((f . f) . map g) xs === (map g . (f . f)) xs
  natural = ?l

mutual

  g : h === h
  g = Refl

  h : g === g
  h = Refl
