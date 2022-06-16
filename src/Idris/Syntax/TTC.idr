module Idris.Syntax.TTC

import public Core.Binary
import public Core.TTC

import TTImp.TTImp
import TTImp.TTImp.TTC

import Idris.Syntax

import Libraries.Data.ANameMap
import Libraries.Data.NameMap
import Libraries.Data.SortedMap
import Libraries.Data.StringMap

%default covering


export
TTC Method where
  toBuf b (MkMethod nm c treq ty)
      = do toBuf b nm
           toBuf b c
           toBuf b treq
           toBuf b ty

  fromBuf b
      = do nm <- fromBuf b
           c <- fromBuf b
           treq <- fromBuf b
           ty <- fromBuf b
           pure (MkMethod nm c treq ty)


export
TTC IFaceInfo where
  toBuf b (MkIFaceInfo ic impps ps cs ms ds)
      = do toBuf b ic
           toBuf b impps
           toBuf b ps
           toBuf b cs
           toBuf b ms
           toBuf b ds

  fromBuf b
      = do ic <- fromBuf b
           impps <- fromBuf b
           ps <- fromBuf b
           cs <- fromBuf b
           ms <- fromBuf b
           ds <- fromBuf b
           pure (MkIFaceInfo ic impps ps cs ms ds)

export
TTC Fixity where
  toBuf b InfixL = tag 0
  toBuf b InfixR = tag 1
  toBuf b Infix = tag 2
  toBuf b Prefix = tag 3

  fromBuf b
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

export
TTC Import where
  toBuf b (MkImport loc reexport path nameAs)
    = do toBuf b loc
         toBuf b reexport
         toBuf b path
         toBuf b nameAs

  fromBuf b
    = do loc <- fromBuf b
         reexport <- fromBuf b
         path <- fromBuf b
         nameAs <- fromBuf b
         pure (MkImport loc reexport path nameAs)

export
TTC SyntaxInfo where
  toBuf b syn
      = do toBuf b (StringMap.toList (infixes syn))
           toBuf b (StringMap.toList (prefixes syn))
           toBuf b (filter (\n => elemBy (==) (fst n) (saveMod syn))
                           (SortedMap.toList $ modDocstrings syn))
           toBuf b (filter (\n => elemBy (==) (fst n) (saveMod syn))
                           (SortedMap.toList $ modDocexports syn))
           toBuf b (filter (\n => fst n `elem` saveIFaces syn)
                           (ANameMap.toList (ifaces syn)))
           toBuf b (filter (\n => isJust (lookup (fst n) (saveDocstrings syn)))
                           (ANameMap.toList (defDocstrings syn)))
           toBuf b (bracketholes syn)
           toBuf b (startExpr syn)
           toBuf b (holeNames syn)

  fromBuf b
      = do inf <- fromBuf b
           pre <- fromBuf b
           moddstr <- fromBuf b
           modexpts <- fromBuf b
           ifs <- fromBuf b
           defdstrs <- fromBuf b
           bhs <- fromBuf b
           start <- fromBuf b
           hnames <- fromBuf b
           pure $ MkSyntax (fromList inf) (fromList pre)
                   [] (fromList moddstr) (fromList modexpts)
                   [] (fromList ifs)
                   empty (fromList defdstrs)
                   bhs
                   [] start
                   hnames
