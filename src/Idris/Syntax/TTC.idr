module Idris.Syntax.TTC

import public Core.Binary
import public Core.TTC

import TTImp.TTImp
import TTImp.TTImp.TTC

import Idris.Syntax

import Libraries.Data.ANameMap
import Libraries.Data.NameMap
import Libraries.Data.NatSet
import Libraries.Data.SortedMap
import Libraries.Data.StringMap

%default covering

export
TTC IFaceInfo where
  toBuf (MkIFaceInfo ic impps ps cs ms ds)
      = do toBuf ic
           toBuf impps
           toBuf ps
           toBuf cs
           toBuf ms
           toBuf ds

  fromBuf
      = do ic <- fromBuf
           impps <- fromBuf
           ps <- fromBuf
           cs <- fromBuf
           ms <- fromBuf
           ds <- fromBuf
           pure (MkIFaceInfo ic impps ps cs ms ds)

export
TTC Fixity where
  toBuf InfixL = tag 0
  toBuf InfixR = tag 1
  toBuf Infix = tag 2
  toBuf Prefix = tag 3

  fromBuf
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

export
TTC Import where
  toBuf (MkImport loc reexport path nameAs)
    = do toBuf loc
         toBuf reexport
         toBuf path
         toBuf nameAs

  fromBuf
    = do loc <- fromBuf
         reexport <- fromBuf
         path <- fromBuf
         nameAs <- fromBuf
         pure (MkImport loc reexport path nameAs)

export
TTC BindingModifier where
  toBuf NotBinding = tag 0
  toBuf Typebind = tag 1
  toBuf Autobind = tag 2
  fromBuf
      = case !getTag of
             0 => pure NotBinding
             1 => pure Typebind
             2 => pure Autobind
             _ => corrupt "binding"

export
TTC FixityInfo where
  toBuf fx
      = do toBuf fx.fc
           toBuf fx.vis
           toBuf fx.bindingInfo
           toBuf fx.fix
           toBuf fx.precedence
  fromBuf
      = do fc <- fromBuf
           vis <- fromBuf
           binding <- fromBuf
           fix <- fromBuf
           prec <- fromBuf
           pure $ MkFixityInfo fc vis binding fix prec


export
TTC SyntaxInfo where
  toBuf syn
      = do toBuf (ANameMap.toList (fixities syn))
           toBuf (filter (\n => elemBy (==) (fst n) (saveMod syn))
                           (SortedMap.toList $ modDocstrings syn))
           toBuf (filter (\n => elemBy (==) (fst n) (saveMod syn))
                           (SortedMap.toList $ modDocexports syn))
           toBuf (filter (\n => fst n `elem` saveIFaces syn)
                           (ANameMap.toList (ifaces syn)))
           toBuf (filter (\n => isJust (lookup (fst n) (saveDocstrings syn)))
                           (ANameMap.toList (defDocstrings syn)))
           toBuf (bracketholes syn)
           toBuf (startExpr syn)
           toBuf (holeNames syn)

  fromBuf
      = do fix <- fromBuf
           moddstr <- fromBuf
           modexpts <- fromBuf
           ifs <- fromBuf
           defdstrs <- fromBuf
           bhs <- fromBuf
           start <- fromBuf
           hnames <- fromBuf
           pure $ MkSyntax (fromList fix)
                   [] (fromList moddstr) (fromList modexpts)
                   [] (fromList ifs)
                   empty (fromList defdstrs)
                   bhs
                   [] start
                   hnames
