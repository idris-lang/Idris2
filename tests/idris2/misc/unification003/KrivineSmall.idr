public export
data EvalContext : Unit -> Type where
  MkEvalContext : EvalContext MkUnit -> EvalContext MkUnit

public export
data Machine : EvalContext MkUnit -> Type where
  Beta : (beta_ctx: EvalContext MkUnit) -> Machine (MkEvalContext beta_ctx)

extract : EvalContext MkUnit -> Unit
-- extract extract_ctx = MkUnit -- no issue
extract (MkEvalContext extract_ctx) = MkUnit

public export
correctness :
  (correctness_ctx : EvalContext MkUnit) ->
  EvalContext (extract correctness_ctx) ->
  Machine correctness_ctx ->
  Unit

correctness .(MkEvalContext eval_ctx) (MkEvalContext eval_ctx_2) (Beta eval_ctx)
  = correctness (believe_me ()) (believe_me ()) (believe_me ())
