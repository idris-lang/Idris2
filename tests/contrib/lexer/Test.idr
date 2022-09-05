import Text.Lexer

data Kind = Ignore | Ident | Oper | Number

ignore : WithBounds (Token Kind) -> Bool
ignore (MkBounded (Tok Ignore _) _ _) = True
ignore _ = False

tmap : TokenMap (Token Kind)
tmap = [
  (alpha <+> many alphaNum, Tok Ident),
  (some digit, Tok Number),
  (some symbol, Tok Oper),
  (spaces, Tok Ignore)
]

show : WithBounds (Token Kind) -> String
show t@(MkBounded (Tok _ v) _ _) = "\{show $ start t} \{show v}"

main : IO ()
main = do
  let toks = filter (not . ignore) $ fst $ lex tmap  "let x = 1\n    y = 2\n in x + y"
  traverse_ (putStrLn . show) toks
