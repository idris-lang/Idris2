||| The content of this module is based on the paper
||| Applications of Applicative Proof Search
||| by Liam O'Connor

module Search.Properties

import Data.So
import Data.Fuel
import public Search.HDecidable

%default total

public export
record Prop (a : Type) where
  constructor MkProp
  runProp : Fuel -> HDec a

public export
interface AProp (0 t : Type -> Type) where
  toProp : t a -> Prop a

public export AProp Prop where toProp = id
public export AProp HDec where toProp = MkProp . const
public export AProp Dec where toProp = MkProp . const . toHDec

public export
check : (f : Fuel) -> (p : Prop a) -> {auto pr : So (isTrue (runProp p f))} -> a
check f p @{pr} = evidence (runProp p f) pr
