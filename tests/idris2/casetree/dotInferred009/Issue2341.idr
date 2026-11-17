import Data.Vect

data Name : Type where
  MkName : String -> Name

data Info : Type where
  EmptyInfo : Info

namespace Variant

  namespace NotIn
    public export
    data NotIn : String -> Vect n String -> Type where
      Nil  : NotIn n []
      (::) : (0 c : Not (n = f)) -> NotIn n fs -> NotIn n (f :: fs)

  public export
  data UniqueNames : (n : Nat) -> Vect n String -> Type where
    Nil  : UniqueNames 0 []
    (::) : NotIn f fs -> UniqueNames n fs -> UniqueNames (S n) (f :: fs)

  public export
  record Variant (a : Type) where
    constructor MkVariant
    size        : Nat
    tags        : Vect size String
    info        : Vect size a
    uniqueTags  : UniqueNames size tags
    nonEmpty    : NonZero size

namespace Typ

  public export
  data Ty : Type where
    Bool    : Ty
    Arr     : Ty -> Ty                -> Ty
    Unit    : Ty
    Tuple   : (n : Nat) -> Vect n Ty  -> Ty
    Variant : (v : Variant Ty)        -> Ty
    List    : Ty                      -> Ty
    LitNat  : Ty

data Context : a -> Type where
  Lin  : Context a
  (:<) : Context a -> a -> Context a

data In : Context a -> a -> Type where
  Z : In (ctx :< a) a
  S : In ctx a -> In (ctx :< b) a

namespace All

  public export
  data All : (0 p : a -> Type) -> Vect n a -> Type where
    Nil  : All p Nil
    (::) : {0 xs : Vect n a} -> p x -> All p xs -> All p (x :: xs)

namespace Variant

  public export
  data VariantTag : String -> Vect n String -> Type where
    Here  : VariantTag t (t :: ts)
    There : VariantTag t ts -> VariantTag t (z :: ts)

  public export
  asFin : {n : Nat} -> {t : String} -> {ts : Vect n String} -> VariantTag t ts -> Fin n
  asFin Here = FZ
  asFin (There x) = FS (asFin x)

  public export
  lookup : {t : String} -> (v : Variant a) -> VariantTag t v.tags -> a
  lookup v g = Vect.index (asFin g) v.info

  public export
  finIdx : {t : String} -> (v : Variant a) -> VariantTag t v.tags -> Fin v.size
  finIdx v g = asFin g

public export
data Tm : Context Ty -> Ty -> Type where

  True : (fi : Info) ->
    {ctx : Context Ty} ->
    ---------------------
         Tm ctx Bool

  False : (fi : Info) ->
    {ctx : Context Ty} ->
    ---------------------
         Tm ctx Bool

  If : (fi : Info) ->
                       {ctx : Context Ty}                   ->
    (p : Tm ctx Bool) -> (t : Tm ctx ty) -> (e : Tm ctx ty) ->
    ----------------------------------------------------------
                          Tm ctx ty

  Var : (fi : Info) ->
     {ctx : Context Ty} ->
          {ty : Ty}     ->
       (k : In ctx ty)  ->
     ---------------------
           Tm ctx ty

  Abs : (fi : Info) ->
        {ctx : Context Ty}     ->
            {ty2 : Ty}         ->
    (var : Name) -> (ty1 : Ty) ->
     (t : Tm (ctx :< ty1) ty2) ->
    -----------------------------
        Tm ctx (Arr ty1 ty2)

  App : (fi : Info) ->
                    {ctx : Context Ty}               ->
                     {ty1, ty2 : Ty}                 ->
    (t1 : Tm ctx (Arr ty1 ty2)) -> (t2 : Tm ctx ty1) ->
    ---------------------------------------------------
                        Tm ctx ty2

  Unit : (fi : Info) ->
    {ctx : Context Ty} ->
    ---------------------
         Tm ctx Unit

  Seq : (fi : Info) ->
                {ctx : Context Ty}         ->
    (t1 : Tm ctx Unit) -> (t2 : Tm ctx ty) ->
    -----------------------------------------
                    Tm ctx ty

  Let : (fi : Info) ->
                      {ctx : Context Ty}                        ->
                        {ty1, ty2 : Ty}                         ->
    (n : Name) -> (t : Tm ctx ty1) -> (b : Tm (ctx :< ty1) ty2) ->
    --------------------------------------------------------------
                          Tm ctx ty2

  Tuple : (fi : Info) ->
    {ctx : Context Ty}  ->
         (n : Nat)      ->
     (tys : Vect n Ty)  ->
      All (Tm ctx) tys  ->
    ----------------------
     Tm ctx (Tuple n tys)

  Proj : (fi : Info) ->
         {ctx : Context Ty}    ->
      (n : Nat) -> (i : Fin n) ->
          {tys : Vect n Ty}    ->
    (t : Tm ctx (Tuple n tys)) ->
    -----------------------------
         Tm ctx (index i tys)

  -- Comment this out for less spaceleak.
  Variant : (fi : Info) ->
          {ctx : Context Ty}    ->
            (tag : String)      ->
           (v : Variant Ty)     ->
    (f : VariantTag tag v.tags) ->
          Tm ctx (lookup v f)   ->
    ------------------------------
        Tm ctx (Variant v)

  -- Comment this out for less spaceleak.
  Case : (fi : Info) ->
             {ctx : Context Ty}           ->
                 {ty : Ty}                ->
              (v : Variant Ty)            ->
           (s : Tm ctx (Variant v))       ->
    (All (\t => Tm (ctx :< t) ty) v.info) ->
    ----------------------------------------
                    Tm ctx ty

  Fix : (fi : Info) ->
    {ctx : Context Ty} ->
    Tm ctx (Arr ty ty) ->
    ---------------------
    Tm ctx ty

  Nil : (fi : Info) ->
    {ctx : Context Ty} ->
         (ty : Ty)     ->
    ---------------------
       Tm ctx (List ty)

  Cons : (fi : Info) ->
           {ctx : Context Ty}     ->
               (ty : Ty)          ->
    Tm ctx ty -> Tm ctx (List ty) ->
    --------------------------------
            Tm ctx (List ty)

  IsNil : (fi : Info) ->
    {ctx : Context Ty} ->
         (ty : Ty)     ->
      Tm ctx (List ty) ->
    ---------------------
         Tm ctx Bool

  Head : (fi : Info) ->
    {ctx : Context Ty} ->
         (ty : Ty)     ->
      Tm ctx (List ty) ->
    ---------------------
          Tm ctx ty

  Tail : (fi : Info) ->
    {ctx : Context Ty} ->
          (ty : Ty)    ->
      Tm ctx (List ty) ->
    ---------------------
       Tm ctx (List ty)

  LitNat : (fi : Info) ->
    {ctx : Context Ty} ->
      (literal : Nat)  ->
    ---------------------
        Tm ctx LitNat

namespace Value

  public export
  data Value : Tm ctx ty -> Type where
    Abs     : Value (Abs fi var ty t)
    True    : Value (True fi)
    False   : Value (False fi)
    Unit    : Value (Unit fi)
    Nil     : Value (Nil fi ty)
    Cons    : (Value h) -> (Value t)   -> Value (Cons fi ty h t)
    Tuple   : {- (vs : App Value ) -> -} Value (Tuple fi n tys tms)
    LitNat  : Value (LitNat fi lit)

data Progress : Tm ctx ty -> Type where
  Value  : (fi : Info) -> (t : Tm ctx ty) -> (tValue : Value t) -> Progress t
  RtmErr : (fi : Info) -> (msg : String) -> (trace : SnocList Info) -> Progress t
  Step  :  (fi : Info)
        -> (tNotValue : Not (Value t))
        -> (t' : Tm ctx ty)
        -> Progress t

0 smallStep : {ty : Ty} -> (t : Tm [<] ty) -> Progress t
smallStep (True fi) = ?smallStep_rhs_0
smallStep (False fi) = ?smallStep_rhs_1
smallStep (If fi p t e) = ?smallStep_rhs_2
smallStep (Var fi k) = ?smallStep_rhs_3
smallStep (Abs fi var ty1 t) = ?smallStep_rhs_4
smallStep (App fi t1 t2) = ?smallStep_rhs_5
smallStep (Unit fi) = ?smallStep_rhs_6
smallStep (Seq fi t1 t2) = ?smallStep_rhs_7
smallStep (Let fi n t b) = ?smallStep_rhs_8
smallStep (Tuple fi n tys x) = ?smallStep_rhs_9
smallStep (Proj fi n i t) = ?smallStep_rhs_10
smallStep (Variant fi tag v f x) = ?smallStep_rhs_11
smallStep (Case fi v s x) = ?smallStep_rhs_12
smallStep (Fix fi x) = ?smallStep_rhs_13
smallStep ([] fi x) = ?smallStep_rhs_14
smallStep (Cons fi x y z) = ?smallStep_rhs_15
smallStep (IsNil fi x y) = ?smallStep_rhs_16
smallStep (Head fi ty y) = ?smallStep_rhs_17
smallStep (Tail fi x y) = ?smallStep_rhs_18
smallStep (LitNat fi literal) = ?smallStep_rhs_19
