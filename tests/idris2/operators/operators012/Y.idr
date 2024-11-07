f : Nat
f =
  let (%^%) : Nat -> Nat -> Nat
      (%^%) = (+)
      private infixl 1 %^%
  in 1 %^% 2

g : Nat
g = do
  let (%^%%) : Nat -> Nat -> Nat
      (%^%%) = (+)
      private infixl 1 %^%%
  1 %^%% 2

crazy1 : Nat
crazy1 = do
  let (%^%%%) : Nat -> Nat -> Nat
      (%^%%%) = (+)
  rewrite let private infixl 1 %^%%% in the (Nat = Nat) Refl
  1 %^%%% 2

crazy2 : List Nat
crazy2 = do
  let (%^%%%%) : Nat -> Nat -> Nat
      (%^%%%%) = (+)
  x : (let private infixl 1 %^%%%% in Nat) <- [1]
  pure $ x %^%%%% 2
