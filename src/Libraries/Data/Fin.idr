module Libraries.Data.Fin

import public Data.Fin

%default total

-- TODO: Remove this, once Data.Fin.strengthen from base is available
--       to the compiler

export
strengthen : {n : _} -> Fin (S n) -> Maybe (Fin n)
strengthen {n = S _} FZ = Just FZ
strengthen {n = S _} (FS p) with (Libraries.Data.Fin.strengthen p)
  strengthen (FS _) | Nothing = Nothing
  strengthen (FS _) | Just q  = Just $ FS q
strengthen _ = Nothing
