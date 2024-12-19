module Libraries.System

import System

-- TODO: Remove this, once `Cast` from `base` is available to the compiler

export
[ToExitCode] Cast Int ExitCode where
  cast code with (code == 0) proof prf
    _ | True = ExitSuccess
    _ | False = ExitFailure code @{rewrite prf in Oh}
