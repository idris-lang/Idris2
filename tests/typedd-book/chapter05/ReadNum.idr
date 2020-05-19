import Data.Strings

readNumber : IO (Maybe Nat)
readNumber = do
  input <- getLine
  if all isDigit (unpack input)
     then pure (Just (stringToNatOrZ input))
     else pure Nothing

readNumbers_v1 : IO (Maybe (Nat, Nat))
readNumbers_v1 =
  do num1 <- readNumber
     case num1 of
          Nothing => pure Nothing
          Just num1_ok =>
               do num2 <- readNumber
                  case num2 of
                       Nothing => pure Nothing
                       Just num2_ok => pure (Just (num1_ok, num2_ok))

readPair : IO (String, String)
readPair = do str1 <- getLine
              str2 <- getLine
              pure (str1, str2)

readNumbers_v2 : IO (Maybe (Nat, Nat))
readNumbers_v2 =
  do Just num1_ok <- readNumber
     Just num2_ok <- readNumber
     pure (Just (num1_ok, num2_ok))

readNumbers : IO (Maybe (Nat, Nat))
readNumbers =
  do Just num1_ok <- readNumber | Nothing => pure Nothing
     Just num2_ok <- readNumber | Nothing => pure Nothing
     pure (Just (num1_ok, num2_ok))
