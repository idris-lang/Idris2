module Issue1012

namespace A

  f : (x : Nat) -> {auto 0 p : Either (x=2) (x=3)} -> ()
  f _ = ()

  g : ()
  g = f 3


namespace B

  fromInteger : Integer -> String

  fw : (x : Nat) -> {auto 0 _ : Either (x=2) (x=3)} -> ()
  fw _ = ()

  gw : ()
  gw = fw 3

namespace C

  fromInteger : Integer -> String

  fw : (x : Nat) -> {auto 0 _ : Either (x=2) (x=3)} -> ()
  fw _ = ()

  gw : ()
  gw = fw (the Nat 3)
