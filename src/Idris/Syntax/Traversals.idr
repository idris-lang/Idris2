module Idris.Syntax.Traversals

import Data.List1

import Idris.Syntax
import Core.Core

import TTImp.TTImp

%default covering

export
mapPTermM : (PTerm' nm -> Core (PTerm' nm)) -> PTerm' nm -> Core (PTerm' nm)
mapPTermM f = goPTerm where

  mutual

    goPTerm : PTerm' nm -> Core (PTerm' nm)
    goPTerm t@(PRef _ _) = f t
    goPTerm (PPi fc x info z argTy retTy) =
      PPi fc x <$> goPiInfo info
               <*> pure z
               <*> goPTerm argTy
               <*> goPTerm retTy
      >>= f
    goPTerm (PLam fc x info pat argTy scope) =
      PLam fc x <$> goPiInfo info
                <*> goPTerm pat
                <*> goPTerm argTy
                <*> goPTerm scope
      >>= f
    goPTerm (PLet fc x pat nTy nVal scope alts) =
      PLet fc x <$> goPTerm pat
                <*> goPTerm nTy
                <*> goPTerm nVal
                <*> goPTerm scope
                <*> goPClauses alts
      >>= f
    goPTerm (PCase fc x xs) =
      PCase fc <$> goPTerm x
               <*> goPClauses xs
      >>= f
    goPTerm (PLocal fc xs scope) =
      PLocal fc <$> goPDecls xs
                <*> goPTerm scope
      >>= f
    goPTerm (PUpdate fc xs) =
      PUpdate fc <$> goPFieldUpdates xs
      >>= f
    goPTerm (PApp fc x y) =
      PApp fc <$> goPTerm x
              <*> goPTerm y
      >>= f
    goPTerm (PWithApp fc x y) =
      PWithApp fc <$> goPTerm x
                  <*> goPTerm y
      >>= f
    goPTerm (PAutoApp fc x y) =
      PAutoApp fc <$> goPTerm x
                         <*> goPTerm y
      >>= f
    goPTerm (PNamedApp fc x n y) =
      PNamedApp fc <$> goPTerm x
                   <*> pure n
                   <*> goPTerm y
      >>= f
    goPTerm (PDelayed fc x y) =
      PDelayed fc x <$> goPTerm y
      >>= f
    goPTerm (PDelay fc x) =
      PDelay fc <$> goPTerm x
      >>= f
    goPTerm (PForce fc x) =
      PForce fc <$> goPTerm x
      >>= f
    goPTerm t@(PSearch _ _) = f t
    goPTerm t@(PPrimVal _ _) = f t
    goPTerm (PQuote fc x) =
      PQuote fc <$> goPTerm x
      >>= f
    goPTerm t@(PQuoteName _ _) = f t
    goPTerm (PQuoteDecl fc x) =
      PQuoteDecl fc <$> traverse goPDecl x
      >>= f
    goPTerm (PUnquote fc x) =
      PUnquote fc <$> goPTerm x
      >>= f
    goPTerm (PRunElab fc x) =
      PRunElab fc <$> goPTerm x
      >>= f
    goPTerm t@(PHole _ _ _) = f t
    goPTerm t@(PType _) = f t
    goPTerm (PAs fc nameFC x pat) =
      PAs fc nameFC x <$> goPTerm pat
      >>= f
    goPTerm (PDotted fc x) =
      PDotted fc <$> goPTerm x
      >>= f
    goPTerm t@(PImplicit _) = f t
    goPTerm t@(PInfer _) = f t
    goPTerm (POp fc opFC x y z) =
      POp fc opFC x <$> goPTerm y
                    <*> goPTerm z
      >>= f
    goPTerm (PPrefixOp fc opFC x y) =
      PPrefixOp fc opFC x <$> goPTerm y
      >>= f
    goPTerm (PSectionL fc opFC x y) =
      PSectionL fc opFC x <$> goPTerm y
      >>= f
    goPTerm (PSectionR fc opFC x y) =
      PSectionR fc opFC <$> goPTerm x
                   <*> pure y
      >>= f
    goPTerm (PEq fc x y) =
      PEq fc <$> goPTerm x
             <*> goPTerm y
      >>= f
    goPTerm (PBracketed fc x) =
      PBracketed fc <$> goPTerm x
      >>= f
    goPTerm (PString fc xs) =
      PString fc <$> goPStrings xs
      >>= f
    goPTerm (PMultiline fc x ys) =
      PMultiline fc x <$> goPStringLines ys
      >>= f
    goPTerm (PDoBlock fc ns xs) =
      PDoBlock fc ns <$> goPDos xs
      >>= f
    goPTerm (PBang fc x) =
      PBang fc <$> goPTerm x
      >>= f
    goPTerm (PIdiom fc ns x) =
      PIdiom fc ns <$> goPTerm x
      >>= f
    goPTerm (PList fc nilFC xs) =
      PList fc nilFC <$> goPairedPTerms xs
      >>= f
    goPTerm (PSnocList fc nilFC xs) =
      PSnocList fc nilFC <$> goPairedSnocPTerms xs
      >>= f
    goPTerm (PPair fc x y) =
      PPair fc <$> goPTerm x
               <*> goPTerm y
      >>= f
    goPTerm (PDPair fc opFC x y z) =
      PDPair fc opFC
                <$> goPTerm x
                <*> goPTerm y
                <*> goPTerm z
      >>= f
    goPTerm t@(PUnit _) = f t
    goPTerm (PIfThenElse fc x y z) =
      PIfThenElse fc <$> goPTerm x
                     <*> goPTerm y
                     <*> goPTerm z
      >>= f
    goPTerm (PComprehension fc x xs) =
      PComprehension fc <$> goPTerm x
                        <*> goPDos xs
      >>= f
    goPTerm (PRewrite fc x y) =
      PRewrite fc <$> goPTerm x
                  <*> goPTerm y
      >>= f
    goPTerm (PRange fc x y z) =
      PRange fc <$> goPTerm x
                <*> goMPTerm y
                <*> goPTerm z
      >>= f
    goPTerm (PRangeStream fc x y) =
      PRangeStream fc <$> goPTerm x
                      <*> goMPTerm y
      >>= f
    goPTerm (PUnifyLog fc k x) =
      PUnifyLog fc k <$> goPTerm x
      >>= f
    goPTerm (PPostfixApp fc rec fields) =
      PPostfixApp fc <$> goPTerm rec <*> pure fields
      >>= f
    goPTerm (PPostfixAppPartial fc fields) =
      f (PPostfixAppPartial fc fields)
    goPTerm (PWithUnambigNames fc ns rhs) =
      PWithUnambigNames fc ns <$> goPTerm rhs
      >>= f

    goPFieldUpdate : PFieldUpdate' nm -> Core (PFieldUpdate' nm)
    goPFieldUpdate (PSetField p t)    = PSetField p <$> goPTerm t
    goPFieldUpdate (PSetFieldApp p t) = PSetFieldApp p <$> goPTerm t

    goPStr : PStr' nm -> Core (PStr' nm)
    goPStr (StrInterp fc t) = StrInterp fc <$> goPTerm t
    goPStr x                = pure x

    goPDo : PDo' nm -> Core (PDo' nm)
    goPDo (DoExp fc t) = DoExp fc <$> goPTerm t
    goPDo (DoBind fc nameFC n t) = DoBind fc nameFC n <$> goPTerm t
    goPDo (DoBindPat fc t u cls) =
      DoBindPat fc <$> goPTerm t
                   <*> goPTerm u
                   <*> goPClauses cls
    goPDo (DoLet fc lhsFC n c t scope) =
       DoLet fc lhsFC n c <$> goPTerm t
                          <*> goPTerm scope
    goPDo (DoLetPat fc pat t scope cls) =
       DoLetPat fc <$> goPTerm pat
                   <*> goPTerm t
                   <*> goPTerm scope
                   <*> goPClauses cls
    goPDo (DoLetLocal fc decls) = DoLetLocal fc <$> goPDecls decls
    goPDo (DoRewrite fc t) = DoRewrite fc <$> goPTerm t

    goPClause : PClause' nm -> Core (PClause' nm)
    goPClause (MkPatClause fc lhs rhs wh) =
      MkPatClause fc <$> goPTerm lhs
                     <*> goPTerm rhs
                     <*> goPDecls wh
    goPClause (MkWithClause fc lhs wps flags cls) =
      MkWithClause fc <$> goPTerm lhs
                      <*> traverseList1 goPWithProblem wps
                      <*> pure flags
                      <*> goPClauses cls
    goPClause (MkImpossible fc lhs) = MkImpossible fc <$> goPTerm lhs

    goPWithProblem : PWithProblem' nm -> Core (PWithProblem' nm)
    goPWithProblem (MkPWithProblem rig wval mnm)
      = MkPWithProblem rig <$> goPTerm wval <*> pure mnm

    goPDecl : PDecl' nm -> Core (PDecl' nm)
    goPDecl (PClaim fc c v opts tdecl) =
      PClaim fc c v <$> goPFnOpts opts
                    <*> goPTypeDecl tdecl
    goPDecl (PDef fc cls) = PDef fc <$> goPClauses cls
    goPDecl (PData fc doc v mbt d) = PData fc doc v mbt <$> goPDataDecl d
    goPDecl (PParameters fc nts ps) =
      PParameters fc <$> go4TupledPTerms nts
                     <*> goPDecls ps
    goPDecl (PUsing fc mnts ps) =
      PUsing fc <$> goPairedPTerms mnts
                <*> goPDecls ps
    goPDecl (PReflect fc t) = PReflect fc <$> goPTerm t
    goPDecl (PInterface fc v mnts n doc nrts ns mn ps) =
      PInterface fc v <$> goPairedPTerms mnts
                      <*> pure n
                      <*> pure doc
                      <*> go3TupledPTerms nrts
                      <*> pure ns
                      <*> pure mn
                      <*> goPDecls ps
    goPDecl (PImplementation fc v opts p is cs n ts mn ns mps) =
      PImplementation fc v opts p <$> goImplicits is
                                  <*> goPairedPTerms cs
                                  <*> pure n
                                  <*> goPTerms ts
                                  <*> pure mn
                                  <*> pure ns
                                  <*> goMPDecls mps
    goPDecl (PRecord fc doc v tot (MkPRecord n nts opts mn fs)) =
      pure $ PRecord fc doc v tot !(MkPRecord n <$> go4TupledPTerms nts
                                                <*> pure opts
                                                <*> pure mn
                                                <*> goPFields fs)
    goPDecl (PRecord fc doc v tot (MkPRecordLater n nts)) =
      pure $ PRecord fc doc v tot (MkPRecordLater n !(go4TupledPTerms nts))
    goPDecl (PFail fc msg ps) = PFail fc msg <$> goPDecls ps
    goPDecl (PMutual fc ps) = PMutual fc <$> goPDecls ps
    goPDecl p@(PFixity _ _ _ _) = pure p
    goPDecl (PNamespace fc strs ps) = PNamespace fc strs <$> goPDecls ps
    goPDecl (PTransform fc n a b) = PTransform fc n <$> goPTerm a <*> goPTerm b
    goPDecl (PRunElabDecl fc a) = PRunElabDecl fc <$> goPTerm a
    goPDecl p@(PDirective _ _) = pure p
    goPDecl p@(PBuiltin _ _ _) = pure p


    goPTypeDecl : PTypeDecl' nm -> Core (PTypeDecl' nm)
    goPTypeDecl (MkPTy fc nameFC n d t) = MkPTy fc nameFC n d <$> goPTerm t

    goPDataDecl : PDataDecl' nm -> Core (PDataDecl' nm)
    goPDataDecl (MkPData fc n t opts tdecls) =
      MkPData fc n <$> goMPTerm t
                   <*> pure opts
                   <*> goPTypeDecls tdecls
    goPDataDecl (MkPLater fc n t) = MkPLater fc n <$> goPTerm t

    goPField : PField' nm -> Core (PField' nm)
    goPField (MkField fc doc c info n t) =
      MkField fc doc c <$> goPiInfo info
                       <*> pure n
                       <*> goPTerm t

    goPiInfo : PiInfo (PTerm' nm) -> Core (PiInfo (PTerm' nm))
    goPiInfo (DefImplicit t) = DefImplicit <$> goPTerm t
    goPiInfo t = pure t

    goPFnOpt : PFnOpt' nm -> Core (PFnOpt' nm)
    goPFnOpt o@(IFnOpt _) = pure o
    goPFnOpt (PForeign ts) = PForeign <$> goPTerms ts
    goPFnOpt (PForeignExport ts) = PForeignExport <$> goPTerms ts

    -- Traversable stuff. Inlined for termination checking.

    goMPTerm : Maybe (PTerm' nm) -> Core (Maybe $ PTerm' nm)
    goMPTerm Nothing  = pure Nothing
    goMPTerm (Just t) = Just <$> goPTerm t

    goPTerms : List (PTerm' nm) -> Core (List $ PTerm' nm)
    goPTerms []        = pure []
    goPTerms (t :: ts) = (::) <$> goPTerm t <*> goPTerms ts

    goPairedPTerms : List (x, PTerm' nm) -> Core (List (x, PTerm' nm))
    goPairedPTerms []             = pure []
    goPairedPTerms ((a, t) :: ts) =
       (::) . MkPair a <$> goPTerm t
                       <*> goPairedPTerms ts

    goPairedSnocPTerms : SnocList (x, PTerm' nm) -> Core (SnocList (x, PTerm' nm))
    goPairedSnocPTerms [<]            = pure [<]
    goPairedSnocPTerms (ts :< (a, t)) =
       (:<) <$> goPairedSnocPTerms ts
            <*> MkPair a <$> goPTerm t

    go3TupledPTerms : List (x, y, PTerm' nm) -> Core (List (x, y, PTerm' nm))
    go3TupledPTerms [] = pure []
    go3TupledPTerms ((a, b, t) :: ts) =
      (::) . (\ c => (a, b, c)) <$> goPTerm t
                                <*> go3TupledPTerms ts

    goImplicits : List (x, y, z, PTerm' nm) ->
                      Core (List (x, y, z, PTerm' nm))
    goImplicits [] = pure []
    goImplicits ((a, b, c, t) :: ts) =
      ((::) . (a,b,c,)) <$> goPTerm t
                        <*> goImplicits ts

    go4TupledPTerms : List (x, y, PiInfo (PTerm' nm), PTerm' nm) ->
                      Core (List (x, y, PiInfo (PTerm' nm), PTerm' nm))
    go4TupledPTerms [] = pure []
    go4TupledPTerms ((a, b, p, t) :: ts) =
      (\ p, d, ts => (a, b, p, d) :: ts) <$> goPiInfo p
                                         <*> goPTerm t
                                         <*> go4TupledPTerms ts

    goPStringLines : List (List (PStr' nm)) -> Core (List (List (PStr' nm)))
    goPStringLines []        = pure []
    goPStringLines (line :: lines) = (::) <$> goPStrings line <*> goPStringLines lines

    goPStrings : List (PStr' nm) -> Core (List (PStr' nm))
    goPStrings []        = pure []
    goPStrings (str :: strs) = (::) <$> goPStr str <*> goPStrings strs

    goPDos : List (PDo' nm) -> Core (List (PDo' nm))
    goPDos []        = pure []
    goPDos (d :: ds) = (::) <$> goPDo d <*> goPDos ds

    goPClauses : List (PClause' nm) -> Core (List (PClause' nm))
    goPClauses []          = pure []
    goPClauses (cl :: cls) = (::) <$> goPClause cl <*> goPClauses cls

    goMPDecls : Maybe (List (PDecl' nm)) -> Core (Maybe (List (PDecl' nm)))
    goMPDecls Nothing   = pure Nothing
    goMPDecls (Just ps) = Just <$> goPDecls ps

    goPDecls : List (PDecl' nm) -> Core (List (PDecl' nm))
    goPDecls []          = pure []
    goPDecls (d :: ds) = (::) <$> goPDecl d <*> goPDecls ds

    goPFieldUpdates : List (PFieldUpdate' nm) -> Core (List (PFieldUpdate' nm))
    goPFieldUpdates []          = pure []
    goPFieldUpdates (fu :: fus) = (::) <$> goPFieldUpdate fu <*> goPFieldUpdates fus

    goPFields : List (PField' nm) -> Core (List (PField' nm))
    goPFields []        = pure []
    goPFields (f :: fs) = (::) <$> goPField f <*> goPFields fs

    goPFnOpts : List (PFnOpt' nm) -> Core (List (PFnOpt' nm))
    goPFnOpts []        = pure []
    goPFnOpts (o :: os) = (::) <$> goPFnOpt o <*> goPFnOpts os

    goPTypeDecls : List (PTypeDecl' nm) -> Core (List (PTypeDecl' nm))
    goPTypeDecls []        = pure []
    goPTypeDecls (t :: ts) = (::) <$> goPTypeDecl t <*> goPTypeDecls ts

export
mapPTerm : (PTerm' nm -> PTerm' nm) -> PTerm' nm -> PTerm' nm
mapPTerm f = goPTerm where

  mutual

    goPTerm : PTerm' nm -> PTerm' nm
    goPTerm t@(PRef _ _) = f t
    goPTerm (PPi fc x info z argTy retTy)
      = f $ PPi fc x (goPiInfo info) z (goPTerm argTy) (goPTerm retTy)
    goPTerm (PLam fc x info z argTy scope)
      = f $ PLam fc x (goPiInfo info) z (goPTerm argTy) (goPTerm scope)
    goPTerm (PLet fc x pat nTy nVal scope alts)
      = f $ PLet fc x (goPTerm pat) (goPTerm nTy) (goPTerm nVal) (goPTerm scope) (goPClause <$> alts)
    goPTerm (PCase fc x xs)
      = f $ PCase fc (goPTerm x) (goPClause <$> xs)
    goPTerm (PLocal fc xs scope)
      = f $ PLocal fc (goPDecl <$> xs) (goPTerm scope)
    goPTerm (PUpdate fc xs)
      = f $ PUpdate fc (goPFieldUpdate <$> xs)
    goPTerm (PApp fc x y)
      = f $ PApp fc (goPTerm x) (goPTerm y)
    goPTerm (PWithApp fc x y)
      = f $ PWithApp fc (goPTerm x) (goPTerm y)
    goPTerm (PAutoApp fc x y)
      = f $ PAutoApp fc (goPTerm x) (goPTerm y)
    goPTerm (PNamedApp fc x n y)
      = f $ PNamedApp fc (goPTerm x) n (goPTerm y)
    goPTerm (PDelayed fc x y)
      = f $ PDelayed fc x (goPTerm y)
    goPTerm (PDelay fc x)
      = f $ PDelay fc $ goPTerm x
    goPTerm (PForce fc x)
      = f $ PForce fc $ goPTerm x
    goPTerm t@(PSearch _ _) = f t
    goPTerm t@(PPrimVal _ _) = f t
    goPTerm (PQuote fc x)
      = f $ PQuote fc $ goPTerm x
    goPTerm t@(PQuoteName _ _) = f t
    goPTerm (PQuoteDecl fc x)
      = f $ PQuoteDecl fc (goPDecl <$> x)
    goPTerm (PUnquote fc x)
      = f $ PUnquote fc $ goPTerm x
    goPTerm (PRunElab fc x)
      = f $ PRunElab fc $ goPTerm x
    goPTerm t@(PHole _ _ _) = f t
    goPTerm t@(PType _) = f t
    goPTerm (PAs fc nameFC x pat)
      = f $ PAs fc nameFC x $ goPTerm pat
    goPTerm (PDotted fc x)
      = f $ PDotted fc $ goPTerm x
    goPTerm t@(PImplicit _) = f t
    goPTerm t@(PInfer _) = f t
    goPTerm (POp fc opFC x y z)
      = f $ POp fc opFC x (goPTerm y) (goPTerm z)
    goPTerm (PPrefixOp fc opFC x y)
      = f $ PPrefixOp fc opFC x $ goPTerm y
    goPTerm (PSectionL fc opFC x y)
      = f $ PSectionL fc opFC x $ goPTerm y
    goPTerm (PSectionR fc opFC x y)
      = f $ PSectionR fc opFC (goPTerm x) y
    goPTerm (PEq fc x y)
      = f $ PEq fc (goPTerm x) (goPTerm y)
    goPTerm (PBracketed fc x)
      = f $ PBracketed fc $ goPTerm x
    goPTerm (PString fc xs)
      = f $ PString fc $ goPStr <$> xs
    goPTerm (PMultiline fc x ys)
      = f $  PMultiline fc x $ map (map goPStr) ys
    goPTerm (PDoBlock fc ns xs)
      = f $ PDoBlock fc ns $ goPDo <$> xs
    goPTerm (PBang fc x)
      = f $ PBang fc $ goPTerm x
    goPTerm (PIdiom fc ns x)
      = f $ PIdiom fc ns $ goPTerm x
    goPTerm (PList fc nilFC xs)
      = f $ PList fc nilFC $ goPairedPTerms xs
    goPTerm (PSnocList fc nilFC xs)
      = f $ PSnocList fc nilFC $ goPairedSnocPTerms xs
    goPTerm (PPair fc x y)
      = f $ PPair fc (goPTerm x) (goPTerm y)
    goPTerm (PDPair fc opFC x y z)
      = f $ PDPair fc opFC (goPTerm x) (goPTerm y) (goPTerm z)
    goPTerm t@(PUnit _) = f t
    goPTerm (PIfThenElse fc x y z)
      = f $ PIfThenElse fc (goPTerm x) (goPTerm y) (goPTerm z)
    goPTerm (PComprehension fc x xs)
      = f $ PComprehension fc (goPTerm x) (goPDo <$> xs)
    goPTerm (PRewrite fc x y)
      = f $ PRewrite fc (goPTerm x) (goPTerm y)
    goPTerm (PRange fc x y z)
      = f $ PRange fc (goPTerm x) (map goPTerm y) (goPTerm z)
    goPTerm (PRangeStream fc x y)
      = f $ PRangeStream fc (goPTerm x) (map goPTerm y)
    goPTerm (PUnifyLog fc k x)
      = f $ PUnifyLog fc k (goPTerm x)
    goPTerm (PPostfixApp fc rec fields)
      = f $ PPostfixApp fc (goPTerm rec) fields
    goPTerm t@(PPostfixAppPartial fc fields) = f t
    goPTerm (PWithUnambigNames fc ns rhs)
      = f $ PWithUnambigNames fc ns (goPTerm rhs)

    goPFieldUpdate : PFieldUpdate' nm -> PFieldUpdate' nm
    goPFieldUpdate (PSetField p t)    = PSetField p $ goPTerm t
    goPFieldUpdate (PSetFieldApp p t) = PSetFieldApp p $ goPTerm t

    goPStr : PStr' nm -> PStr' nm
    goPStr (StrInterp fc t) = StrInterp fc $ goPTerm t
    goPStr x                = x

    goPDo : PDo' nm -> PDo' nm
    goPDo (DoExp fc t) = DoExp fc $ goPTerm t
    goPDo (DoBind fc nameFC n t) = DoBind fc nameFC n $ goPTerm t
    goPDo (DoBindPat fc t u cls)
      = DoBindPat fc (goPTerm t) (goPTerm u) (goPClause <$> cls)
    goPDo (DoLet fc lhsFC n c t scope)
      = DoLet fc lhsFC n c (goPTerm t) (goPTerm scope)
    goPDo (DoLetPat fc pat t scope cls)
      = DoLetPat fc (goPTerm pat) (goPTerm t) (goPTerm scope) (goPClause <$> cls)
    goPDo (DoLetLocal fc decls) = DoLetLocal fc $ goPDecl <$> decls
    goPDo (DoRewrite fc t) = DoRewrite fc $ goPTerm t

    goPWithProblem : PWithProblem' nm -> PWithProblem' nm
    goPWithProblem (MkPWithProblem rig wval mnm)= MkPWithProblem rig (goPTerm wval) mnm

    goPClause : PClause' nm -> PClause' nm
    goPClause (MkPatClause fc lhs rhs wh)
      = MkPatClause fc (goPTerm lhs) (goPTerm rhs) (goPDecl <$> wh)
    goPClause (MkWithClause fc lhs wps flags cls)
      = MkWithClause fc (goPTerm lhs) (goPWithProblem <$> wps) flags (goPClause <$> cls)
    goPClause (MkImpossible fc lhs) = MkImpossible fc $ goPTerm lhs

    goPDecl : PDecl' nm -> PDecl' nm
    goPDecl (PClaim fc c v opts tdecl)
      = PClaim fc c v (goPFnOpt <$> opts) (goPTypeDecl tdecl)
    goPDecl (PDef fc cls) = PDef fc $ goPClause <$> cls
    goPDecl (PData fc doc v mbt d) = PData fc doc v mbt $ goPDataDecl d
    goPDecl (PParameters fc nts ps)
      = PParameters fc (go4TupledPTerms nts) (goPDecl <$> ps)
    goPDecl (PUsing fc mnts ps)
      = PUsing fc (goPairedPTerms mnts) (goPDecl <$> ps)
    goPDecl (PReflect fc t) = PReflect fc $ goPTerm t
    goPDecl (PInterface fc v mnts n doc nrts ns mn ps)
      = PInterface fc v (goPairedPTerms mnts) n doc (go3TupledPTerms nrts) ns mn (goPDecl <$> ps)
    goPDecl (PImplementation fc v opts p is cs n ts mn ns mps)
      = PImplementation fc v opts p (goImplicits is) (goPairedPTerms cs)
           n (goPTerm <$> ts) mn ns (map (goPDecl <$>) mps)
    goPDecl (PRecord fc doc v tot (MkPRecord n nts opts mn fs))
      = PRecord fc doc v tot (MkPRecord n (go4TupledPTerms nts) opts mn (goPField <$> fs))
    goPDecl (PRecord fc doc v tot (MkPRecordLater n nts))
      = PRecord fc doc v tot (MkPRecordLater n (go4TupledPTerms nts))
    goPDecl (PFail fc msg ps) = PFail fc msg $ goPDecl <$> ps
    goPDecl (PMutual fc ps) = PMutual fc $ goPDecl <$> ps
    goPDecl p@(PFixity _ _ _ _) = p
    goPDecl (PNamespace fc strs ps) = PNamespace fc strs $ goPDecl <$> ps
    goPDecl (PTransform fc n a b) = PTransform fc n (goPTerm a) (goPTerm b)
    goPDecl (PRunElabDecl fc a) = PRunElabDecl fc $ goPTerm a
    goPDecl p@(PDirective _ _) = p
    goPDecl p@(PBuiltin _ _ _) = p


    goPTypeDecl : PTypeDecl' nm -> PTypeDecl' nm
    goPTypeDecl (MkPTy fc nameFC n d t) = MkPTy fc nameFC n d $ goPTerm t

    goPDataDecl : PDataDecl' nm -> PDataDecl' nm
    goPDataDecl (MkPData fc n t opts tdecls)
      = MkPData fc n (map goPTerm t) opts (goPTypeDecl <$> tdecls)
    goPDataDecl (MkPLater fc n t) = MkPLater fc n $ goPTerm t

    goPField : PField' nm -> PField' nm
    goPField (MkField fc doc c info n t)
      = MkField fc doc c (goPiInfo info) n (goPTerm t)

    goPiInfo : PiInfo (PTerm' nm) -> PiInfo (PTerm' nm)
    goPiInfo (DefImplicit t) = DefImplicit $ goPTerm t
    goPiInfo t = t

    goPFnOpt : PFnOpt' nm -> PFnOpt' nm
    goPFnOpt o@(IFnOpt _) = o
    goPFnOpt (PForeign ts) = PForeign $ goPTerm <$> ts
    goPFnOpt (PForeignExport ts) = PForeignExport $ goPTerm <$> ts

    goPairedPTerms : List (x, PTerm' nm) -> List (x, PTerm' nm)
    goPairedPTerms [] = []
    goPairedPTerms ((a, t) :: ts) = (a, goPTerm t) :: goPairedPTerms ts

    goPairedSnocPTerms : SnocList (x, PTerm' nm) -> SnocList (x, PTerm' nm)
    goPairedSnocPTerms [<] = [<]
    goPairedSnocPTerms (ts :< (a, t)) = goPairedSnocPTerms ts :< (a, goPTerm t)

    go3TupledPTerms : List (x, y, PTerm' nm) -> List (x, y, PTerm' nm)
    go3TupledPTerms [] = []
    go3TupledPTerms ((a, b, t) :: ts) = (a, b, goPTerm t) :: go3TupledPTerms ts

    goImplicits : List (x, y, z, PTerm' nm) -> List (x, y, z, PTerm' nm)
    goImplicits [] = []
    goImplicits ((a, b, c, t) :: ts) = (a,b,c, goPTerm t) :: goImplicits ts

    go4TupledPTerms : List (x, y, PiInfo (PTerm' nm), PTerm' nm) ->
                      List (x, y, PiInfo (PTerm' nm), PTerm' nm)
    go4TupledPTerms [] = []
    go4TupledPTerms ((a, b, p, t) :: ts)
      = (a, b, goPiInfo p, goPTerm t) :: go4TupledPTerms ts

||| Replace the FCs in a term with the one provided.
||| The current implementation is not correct: we're only substituting
||| in PTerm but it should be enough for our purposes (making sure the
||| ellipsis used in a with clause's LHS refers to the correct line).
export
substFC : FC -> PTerm' nm -> PTerm' nm
substFC fc = mapPTerm $ \case
  PRef _ x => PRef fc x
  PPi _ x y z argTy retTy => PPi fc x y z argTy retTy
  PLam _ x y pat argTy scope => PLam fc x y pat argTy scope
  PLet _ x pat nTy nVal scope alts => PLet fc x pat nTy nVal scope alts
  PCase _ x xs => PCase fc x xs
  PLocal _ xs scope => PLocal fc xs scope
  PUpdate _ xs => PUpdate fc xs
  PApp _ x y => PApp fc x y
  PWithApp _ x y => PWithApp fc x y
  PNamedApp _ x n y => PNamedApp fc x n y
  PAutoApp _ x y => PAutoApp fc x y
  PDelayed _ x y => PDelayed fc x y
  PDelay _ x => PDelay fc x
  PForce _ x => PForce fc x
  PSearch _ depth => PSearch fc depth
  PPrimVal _ x => PPrimVal fc x
  PQuote _ x => PQuote fc x
  PQuoteName _ n => PQuoteName fc n
  PQuoteDecl _ xs => PQuoteDecl fc xs
  PUnquote _ x => PUnquote fc x
  PRunElab _ x => PRunElab fc x
  PHole _ bracket holename => PHole fc bracket holename
  PType _ => PType fc
  PAs _ _ n pattern => PAs fc fc n pattern
  PDotted _ x => PDotted fc x
  PImplicit _ => PImplicit fc
  PInfer _ => PInfer fc
  POp _ _ x y z => POp fc fc x y z
  PPrefixOp _ _ x y => PPrefixOp fc fc x y
  PSectionL _ _ x y => PSectionL fc fc x y
  PSectionR _ _ x y => PSectionR fc fc x y
  PEq _ x y => PEq fc x y
  PBracketed _ x => PBracketed fc x
  PString _ xs => PString fc xs
  PMultiline _ indent xs => PMultiline fc indent xs
  PDoBlock _ x xs => PDoBlock fc x xs
  PBang _ x => PBang fc x
  PIdiom _ x y => PIdiom fc x y
  PList _ _ xs => PList fc fc xs
  PSnocList _ _ sx => PSnocList fc fc sx
  PPair _ x y => PPair fc x y
  PDPair _ _ x y z => PDPair fc fc x y z
  PUnit _ => PUnit fc
  PIfThenElse _ x y z => PIfThenElse fc x y z
  PComprehension _ x xs => PComprehension fc x xs
  PRewrite _ x y => PRewrite fc x y
  PRange _ x y z => PRange fc x y z
  PRangeStream _ x y => PRangeStream fc x y
  PPostfixApp _ x xs => PPostfixApp fc x xs
  PPostfixAppPartial _ xs => PPostfixAppPartial fc xs
  PUnifyLog _ x y => PUnifyLog fc x y
  PWithUnambigNames _ xs x => PWithUnambigNames fc xs x
