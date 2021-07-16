module TestException

import Control.App

throwBoth : Has [Exception String, Exception Int] es => App es ()

throwOne : Has [Exception Int] es => App es Int
throwOne {es} = handle {err = String} {e = es} throwBoth (\r => pure 1) (\e => pure 3)
