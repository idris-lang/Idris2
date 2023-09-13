module DelayParse

public export
data MyStream : Type where
  (::) :  (anA : a)
       -> (nextA : a -> a)
       -> Inf MyStream
       -> MyStream

public export
go : a -> (a -> a) -> MyStream
go initA fn =
  MyStream.(::) initA fn (Delay (fn initA) fn)
