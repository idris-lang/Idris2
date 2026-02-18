namespace A
  public export
  pure : a -> IO a
  pure x = io_pure x

  public export
  (<*>) : IO (a -> b) -> IO a -> IO b
  (<*>) = (<*>) @{%search}

namespace B
  public export
  pure : a -> IO a
  pure x = io_pure x

  public export
  (<*>) : IO (a -> b) -> IO a -> IO b
  (<*>) = (<*>) @{%search}

testFailing1 : IO ()
testFailing1 = pure ()

testSucceeding1 : IO ()
testSucceeding1 = A.do
  pure ()

testFailing2 : (a -> b) -> IO a -> IO b
testFailing2 f a =
  [| f a |]

testSucceeding2 : (a -> b) -> IO a -> IO b
testSucceeding2 f a = B.do
  [| f a |]
