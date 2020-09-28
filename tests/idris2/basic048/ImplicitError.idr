module ImplicitError

%logging elab.generalise 20

namespace Foo

  f : Either a b -> Either b a
  f (Left a) = Right a
  f (Right b) = Left b

namespace Goo

  natural : (xs : Either a b) -> ((f . f) . map g) xs === (map g . (f . f)) xs
  natural = ?natural_0 -- f has been generalised this is not provable

namespace Hoo

  f : Either a b -> Either b a
  f (Left a) = Right a
  f (Right b) = Left b

  -- bug: f should *not* have been generalised!
  natural : (xs : Either a b) -> ((f . f) . map g) xs === (map g . (f . f)) xs
  natural = ?natural_1

{-
  natural (Left a) = Refl
  natural (Right b) = Refl
-}


f : Either a b -> Either b a
f (Left a) = Right a
f (Right b) = Left b

-- properly functioning: f has not been generalised
natural : (xs : Either a b) -> ((f . f) . map g) xs === (map g . (f . f)) xs
natural (Left a) = Refl
natural (Right b) = Refl
