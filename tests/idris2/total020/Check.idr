record RF infot where
  constructor MkRF
  info : infot
  op : RF infot -> RF infot

total
test : RF a -> (a -> RF b) -> RF b
test a f = let foo = f a.info in foo

total
test2 : RF a -> (a -> RF b) -> RF b
test2 a f = f a.info

total
test3 : RF a -> (a -> RF b) -> RF b
test3 a f = let foo = a in f foo.info

total
test4 : RF a -> (a -> RF b) -> RF b
test4 a f = let foo : RF b
                foo = f a.info
             in foo

