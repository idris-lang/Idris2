module Idris.IDEMode.Commands

import Core.Core
import Core.Context
import Core.Context.Log
import Core.Name
import public Idris.REPL.Opts
import Protocol.Hex

import System.File

import public Protocol.IDE
import public Protocol.SExp

%default total

export
getMsg : SExp -> Maybe (IDECommand, Integer)
getMsg (SExpList [cmdexp, IntegerAtom num])
   = do cmd <- fromSExp cmdexp
        pure (cmd, num)
getMsg _ = Nothing

export
SExpable Name where
  toSExp = SymbolAtom . show

export
version : Int -> Int -> SExp
version maj min = toSExp $ Version maj min

sendStr : File -> String -> IO ()
sendStr f st =
  map (const ()) (fPutStr f st)

export                          -- v---- ought to become a message
send : {auto c : Ref Ctxt Defs} -> SExpable a => File -> a -> Core ()
send f resp
    = do let r = show (toSExp resp) ++ "\n"
         log "ide-mode.send" 20 r
         coreLift $ sendStr f $ leftPad '0' 6 (asHex (cast (length r)))
         coreLift $ sendStr f r
         coreLift $ fflush f
