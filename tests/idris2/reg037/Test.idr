module Test

data A = A0

giveA : HasIO io => io A
giveA = pure A0

please : HasIO io => io ()
please = do
     value_a <- giveA

     let a : A
         a = value_a

     pure ()

interface Cool a where cool : a -> a
implementation Cool A where cool x = x

help : A
help = cool (let x : String; x = "hello" in A0)
