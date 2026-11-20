namespace Notation
  public export
  data Notation : Type where
    Nil : Notation
    (>>) : Notation -> Notation -> Notation

    Emp : Notation
    Snoc : (restTy, topTy : Notation) -> Notation
    Pi : (inputTy, outputTy : Notation) -> Notation
    Sig : (fstTy, sndTy : Notation) -> Notation

    Dup : Notation
    Drop : Notation
    Dip : Notation -> Notation
    One, Zero, Nat : Notation
    Typ : Notation

    S : Notation
    Z : Notation

    The : Notation

    Absurd : Notation

    Quote : Notation -> Notation

data Syntax : (s : Notation) -> (e : Notation) -> (t : Notation) -> Type where
  Pi :
    {0 t : _} ->
    (inputTyJ : Syntax s inputTy (Snoc t Typ)) ->
    (
      Syntax
        s
        outputTy
        (Snoc u Typ)
    ) ->
    Syntax s (Pi inputTy outputTy) (Snoc s Typ)
  Dip :
    Syntax s e t ->
    Syntax
      (Snoc s a)
      (Dip e)
      (Snoc (Drop >> t) ((Drop >> t) >> Drop >> a))
  Drop : Syntax (Snoc s a) Drop s
  One : Syntax s One (Snoc s Typ)

partial
0 safe : Syntax s e t -> ()
safe (Pi inputTyJ x) = ?safe_rhs_3
safe (Dip x) = ?safe_rhs_5
safe Drop = ?safe_rhs_6
safe One = ?safe_rhs_7
