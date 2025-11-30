%default total

trythis : (mb : Maybe Bool) -> mb === Just True -> Void
trythis Nothing ab = absurd ab

boom : Void
boom = trythis (Just True) Refl
