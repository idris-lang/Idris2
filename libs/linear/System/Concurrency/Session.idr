module System.Concurrency.Session

import Control.Linear.LIO

import Data.List.AtIndex
import Data.Nat

import Data.OpenUnion
import System
import System.File
import System.Concurrency as Threads
import System.Concurrency.Linear

import Language.Reflection

%default total

------------------------------------------------------------------------
-- Session types

namespace Session

  ||| A session type describes the interactions one thread may have with
  ||| another over a shared bidirectional channel: it may send or receive
  ||| values of arbitrary types, or be done communicating.
  public export
  data Session : Type where
    Send : (ty : Type) -> (s : Session) -> Session
    Recv : (ty : Type) -> (s : Session) -> Session
    End  : Session

  ||| Dual describes how the other party to the communication sees the
  ||| interactions: our sends become their receives and vice-versa.
  public export
  Dual : Session -> Session
  Dual (Send ty s) = Recv ty (Dual s)
  Dual (Recv ty s) = Send ty (Dual s)
  Dual End = End

  ||| Duality is involutive: the dual of my dual is me
  export
  dualInvolutive : (s : Session) -> Dual (Dual s) === s
  dualInvolutive (Send ty s) = cong (Send ty) (dualInvolutive s)
  dualInvolutive (Recv ty s) = cong (Recv ty) (dualInvolutive s)
  dualInvolutive End = Refl

||| We can collect the list of types that will be sent over the
||| course of a session by walking down its description
||| This definition is purely internal and will not show up in
||| the library's interface.
SendTypes : Session -> List Type
SendTypes (Send ty s) = ty :: SendTypes s
SendTypes (Recv ty s) = SendTypes s
SendTypes End = []

||| We can collect the list of types that will be received over
||| the course of a session by walking down its description
||| This definition is purely internal and will not show up in
||| the library's interface.
RecvTypes : Session -> List Type
RecvTypes (Send ty s) = RecvTypes s
RecvTypes (Recv ty s) = ty :: RecvTypes s
RecvTypes End = []

||| The types received by my dual are exactly the ones I am sending
||| This definition is purely internal and will not show up in
||| the library's interface.
RecvDualTypes : (s : Session) -> RecvTypes (Dual s) === SendTypes s
RecvDualTypes (Send ty s) = cong (ty ::) (RecvDualTypes s)
RecvDualTypes (Recv ty s) = RecvDualTypes s
RecvDualTypes End = Refl

||| The types sent by my dual are exactly the ones I receive
||| This definition is purely internal and will not show up in
||| the library's interface.
SendDualTypes : (s : Session) -> SendTypes (Dual s) === RecvTypes s
SendDualTypes (Send ty s) = SendDualTypes s
SendDualTypes (Recv ty s) = cong (ty ::) (SendDualTypes s)
SendDualTypes End = Refl

namespace Seen

  ||| The inductive family (Seen m n f) states that the function `f`
  ||| was obtained by composing an interleaving of `m` receiving
  ||| steps and `n` sending ones.
  public export
  data Seen : Nat -> Nat -> (Session -> Session) -> Type where
    None : Seen 0 0 Prelude.id
    Recv : (ty : Type) -> Seen m n f -> Seen (S m) n (f . Recv ty)
    Send : (ty : Type) -> Seen m n f -> Seen m (S n) (f . Send ty)

||| If we know that `ty` is at index `n` in the list of received types
||| and that `f` is a function defined using an interleaving of steps
||| comprising `m` receiving stepsx then `ty` is at index `m + n` in `f s`.
atRecvIndex : Seen m _ f ->
          (s : Session) ->
          AtIndex ty (RecvTypes s) n ->
          AtIndex ty (RecvTypes (f s)) (m + n)
atRecvIndex None accS accAt = accAt
atRecvIndex (Recv ty s) accS accAt
  = rewrite plusSuccRightSucc (pred m) n in
    atRecvIndex s (Recv ty accS) (S accAt)
atRecvIndex (Send ty s) accS accAt
  = atRecvIndex s (Send ty accS) accAt

||| If we know that `ty` is at index `n` in the list of sent types
||| and that `f` is a function defined using an interleaving of steps
||| comprising `m` sending steps then `ty` is at index `m + n` in `f s`.
atSendIndex : Seen _ m f ->
          (s : Session) ->
          AtIndex ty (SendTypes s) n ->
          AtIndex ty (SendTypes (f s)) (m + n)
atSendIndex None accS accAt = accAt
atSendIndex (Recv ty s) accS accAt
  = atSendIndex s (Recv ty accS) accAt
atSendIndex (Send ty s) accS accAt
  = rewrite plusSuccRightSucc (pred m) n in
    atSendIndex s (Send ty accS) (S accAt)


||| A (bidirectional) channel is parametrised by a session it must respect.
|||
||| It is implemented in terms of two low-level channels: one for sending
||| and one for receiving. This ensures that we never are in a situation
||| where a thread with session (Send Nat (Recv String ...)) sends a natural
||| number and subsequently performs a receive before the other party
||| to the communication had time to grab the Nat thus receiving it
||| instead of a String.
|||
||| The low-level channels can only carry values of a single type. And so
||| they are given respective union types corresponding to the types that
||| can be sent on the one hand and the ones that can be received on the
||| other.
||| These union types are tagged unions where if `ty` is at index `k` in
||| the list of types `tys` then `(k, v)` is a value of `Union tys` provided
||| that `v` has type `ty`.
|||
||| `sendStep`, `recvStep`, `seePrefix`, and `seen` encode the fact that
||| we have already performed some of the protocol and so the low-level
||| channels' respective types necessarily mention types that we won't
||| see anymore.
export
record Channel (s : Session) where
  constructor MkChannel
  {sendStep     : Nat}
  {recvStep     : Nat}
  {0 seenPrefix : Session -> Session}
  0 seen        : Seen recvStep sendStep seenPrefix

  sendChan : Threads.Channel (Union (SendTypes (seenPrefix s)))
  recvChan : Threads.Channel (Union (RecvTypes (seenPrefix s)))

||| Consume a linear channel with a `Recv ty` step at the head of the
||| session type in order to obtain a value of type `ty` together with
||| a linear channel for the rest of the session.
export
recv : LinearIO io =>
  Channel (Recv ty s) -@
  L1 io (Res ty (const (Channel s)))
recv (MkChannel {recvStep} seen sendCh recvCh) = do
  x@(Element k prf val) <- channelGet recvCh
  -- Here we check that we got the right message by projecting out of
  -- the union type using the current `recvStep`. Both ends should be
  -- in sync because of the `RecvDualTypes` and `SendDualTypes` lemmas.
  let Just val = prj (recvStep + 0) (atRecvIndex seen (Recv ty s) Z) x
    | Nothing => die1 "Error: invalid recv expected \{show recvStep} but got \{show k}"
  pure1 (val # MkChannel (Recv ty seen) sendCh recvCh)


||| Consume a linear channel with a `Send ty` step at the head of the
||| session type in order to send a value of type `ty` and obtain a
||| linear channel for the rest of the session.
export
send : LinearIO io =>
  (1 _ : Channel (Send ty s)) ->
  ty ->
  L1 io (Channel s)
send (MkChannel {sendStep} seen sendCh recvCh) x = do
  let val = inj (sendStep + 0) (atSendIndex seen (Send ty s) Z) x
  channelPut sendCh val
  pure1 (MkChannel (Send ty seen) sendCh recvCh)

||| Discard the channel provided that the session has reached its `End`.
export
end : LinearIO io => Channel End -@ L io ()
end (MkChannel _ _ _) = do
  pure ()

||| Given a session, create a bidirectional communication channel and
||| return its two endpoints
export
makeChannel :
  LinearIO io =>
  (0 s : Session) ->
  L1 io (LPair (Channel s) (Channel (Dual s)))
makeChannel s = do
  sendChan <- Threads.makeChannel
  recvChan <- Threads.makeChannel
  let 1 posCh : Channel s
    := MkChannel None sendChan recvChan
  let 1 negCh : Channel (Dual s)
    := MkChannel None
         (rewrite SendDualTypes s in recvChan)
         (rewrite RecvDualTypes s in sendChan)
  pure1 (posCh # negCh)

||| Given a session and two functions communicating according to that
||| session, we can run the two programs concurrently and collect their
||| final results.
export
fork : (0 s : Session) ->
       (Channel       s  -@ L IO a) -@
       (Channel (Dual s) -@ L IO b) -@
       L IO (a, b)
fork s kA kB = do
  let 1 io = makeChannel s
  (posCh # negCh) <- io
  par (kA posCh) (kB negCh)
