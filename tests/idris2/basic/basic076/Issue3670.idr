import Data.Vect

public export
data Chain : (len : Nat) -> (t : Nat -> Type -> Type)
  -> (item : Type)
  -> (m : forall a, b, c . t a c -> t b c -> Type)
  -> (input : t a' item) -> (output : t b' item) -> Type where
  Same : {m : forall a, b, c . t a c -> t b c -> Type} -> Chain 0 t item m x x
  Apply : {m : forall a, b, c . t a c -> t b c -> Type}
    -> (prev : Chain len t item m input intermediate) -> (modification : m intermediate output)
    -> Chain (S len) t item m input output

public export
interface LawfulChain (t : Nat -> Type -> Type)
  (m : forall a, b, c . t a c -> t b c -> Type) | m where
  apply : (input : t len_input item)
    -> {0 output : t len_output item} -> (chain : Chain len_chain t item m input output)
    -> t len_output item
  applyCorrect : (input : t len_input item)
    -> {0 output : t len_output item} -> (chain : Chain len_chain t item m input output)
    -> (apply input chain) = output

public export
data Modification : Vect n item -> Vect m item -> Type where
  Insert : {0 prev : Vect n item} -> (idx : Fin (S n)) -> (it : item)
    -> Modification prev (insertAt idx it prev)
  Delete : {0 prev : Vect (S n) item} -> (idx : Fin (S n))
    -> Modification prev (deleteAt idx prev)

public export
LawfulChain Vect Modification where
  apply input Same = input
  apply input (Apply prev (Insert idx it)) = insertAt idx it (apply input prev)
  apply input (Apply prev (Delete idx)) = deleteAt idx (apply input prev)
  applyCorrect input chain = ?applyCorrect_rhs
