||| This module is based on the content of the functional pearl
||| How to Take the Inverse of a Type
||| by Daniel Marshall and Dominic Orchard

module Data.Linear.Communications

import Data.Linear
import Data.Linear.Inverse

%default total

-- Communicating with Inverses

-- Session type
public export
data Protocol : Type where
  Send : Type -> Protocol -> Protocol
  Recv : Type -> Protocol -> Protocol
  End : Protocol

public export
Dual : Protocol -> Protocol
Dual (Send x s) = Recv x (Dual s)
Dual (Recv x s) = Send x (Dual s)
Dual End = End

export
data LChan : Protocol -> Type where
  MkLChan : {- pointer or something  -@ -} LChan p

parameters
  -- Assuming we have these primitives acting on channels
  (send : forall s, a. LChan (Send a s) -@ a -@ LChan s)
  (recv : forall s, a. LChan (Recv a s) -@ LPair a (LChan s))
  (close : LChan End -@ ())
  -- Fork relates inverse & duality
  (fork : (0 s : Protocol) -> Inverse (LChan s) -@ LChan (Dual s))

  -- We can write double negation elimination by communicating
  involOp : Inverse (Inverse a) -@ a
  involOp k =
    let 0 P : Protocol
        P = Send a End
        1 r : LChan (Dual P)
            := fork P $ mkInverse $ \ s =>
                (`divide` k) $ mkInverse $
                \ x => let 1 c = send s x in close c
        (x # c') := recv r
        () := close c'
     in x
