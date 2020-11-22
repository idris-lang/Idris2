||| During elaboration, we lift local definitions to the top left, and
||| replace references to them with calls to the lifted definition
||| passing the current environment as an argument.
|||
||| This causes a problem with AutoSearch calls: we don't know in
||| advance where we will call these lifted definitions. To do that,
||| we need the opposite operation for lowering such a lifted
||| definition back to the environment in which it was defined.
|||
||| Lowering gets more complicated since lifted definitions are stored
||| at the top level, after we already forgot about the current
||| environment, so we need to reconstruct it. In the current design,
||| we only store the depth of the environment at the local
||| definition.
|||
||| The whole thing is a hack, the right way to deal with it is
||| probably to just not lift local definitions and dependent pattern
||| matching to the top-level, but leave them in-place until code
||| generation. Perhaps in a future version of Idris.
module Core.Lower

import Core.Context
import Core.Context.Log
import Core.Core
import Core.Env
import Core.Normalise
import Core.TT
import Core.Value

import Data.Bool.Extra
import Data.Either
import Data.List
import Data.List.Equalities -- Is it ok to depend on contrib?
import Data.Maybe
import Data.DPair

import Data.Nat
import Data.Nat
import Data.Nat.Order
import Data.Nat.Order.Properties -- are we comfortable with deps on contrib?

import Syntax.PreorderReasoning  -- ditto
import Data.List.Equalities      -- ditto
import Data.List.Reverse         -- ditto
import Decidable.Order
 
%default covering

InvariantViolation : Nat -> Error
InvariantViolation n = InternalError 
                      $ "Internal invariant failed, please report issue referring to"
                      ++ "cc175bb3bdba:" ++ (show n)
  
peelAux : {auto c : Ref Ctxt Defs} -> SizeOf liftedVars -> Term peeledVars 
     -> Core $ Exists $ \rest => Term rest `Subset` 
               (const $ rest === (reverseOnto peeledVars liftedVars))
peelAux {liftedVars = []} {peeledVars} 
     (MkSizeOf _  Z   ) tm 
     = pure $ Evidence _ (tm `Element` Refl)
peelAux {liftedVars = x :: liftedVars} sz@(MkSizeOf (S n) (S n')) 
     (Bind _ argName (Pi fc _ _ ty) scope) = do
       tmPrf <- peelAux (MkSizeOf n n') $ renameVars (CompatExt CompatPre) scope
       pure $ Evidence _ (fst (snd tmPrf) `Element` (snd (snd tmPrf)))
peelAux {liftedVars = x :: liftedVars} (MkSizeOf _ (S n)) _ = 
      -- This means that the depth stored in typeHints is somehow wrong, likely the depth
      -- stored in typeHints is deeper than the current environment.
           throw $ InvariantViolation 0
           
peel : {auto c : Ref Ctxt Defs} -> SizeOf liftedVars -> Term [] -> Core (Term liftedVars)
peel {liftedVars} n closedTy = do
  heavyWork <- peelAux (reverse n) closedTy
  -- Extract the information to convince idris we're done
  (let 0 rest : List Name
       rest = fst heavyWork
       ty : Term rest
       ty = fst (snd heavyWork)
       0 rest_is_liftedVars : rest = liftedVars
       rest_is_liftedVars = Calc $
         |~ rest
         ~~ reverse (reverse liftedVars) ...(snd (snd heavyWork))
         ~~ liftedVars                   ...(reverseReverseId liftedVars)
   in pure $ rewrite sym rest_is_liftedVars in
             ty)

partial
lower : {vars' : _} -> {auto c : Ref Ctxt Defs} -> FC -> Term [] -> Term vars' -> (env' : Env Term vars') -> (envDepth : Nat) 
     -> Core (Term vars', Term vars') 
%unbound_implicits off     
lower         fc liftedTy tm env' 0 = pure (embed liftedTy, tm)
lower {vars'} fc liftedTy tm env' envDepth = 
  let len : Nat
      len = length env'
  in do
  let Yes d_lte_len = decideLTE envDepth len
  | No _ => throw $ InvariantViolation 1
  log "auto" 10 $ "checksum for lowering fine: " ++ (show envDepth) ++ " <= " ++ (show len)
  (let prefixLen : Nat
       prefixLen = len `minus` envDepth
       -- We're going to need to convince Idris the terms we construct are well-formed
       -- some arithmetic first
       0 len_is_len : (length env' = length vars')
       len_is_len = lengthInvariant env'
       0 prefixLen_lte_len : prefixLen `LTE` (length vars')
       prefixLen_lte_len = replace {p = \ n => (len `minus` envDepth) `LTE` n} 
                              len_is_len $
                              minusLTE envDepth len
       0 suffixVars : List Name
       suffixVars = drop prefixLen vars' 
       0 keptVars : List Name
       keptVars = take prefixLen vars' 
          
       0 prefixLen_is_len : (length keptVars = prefixLen)
       prefixLen_is_len = reflectLength $ snd $ specTakeDrop prefixLen vars' prefixLen_lte_len
          
       0 varsDecomposition : (vars' = keptVars ++ suffixVars)
       varsDecomposition = fst $ specTakeDrop prefixLen vars' prefixLen_lte_len
       0 suffixLen_is_depth : (length suffixVars = envDepth)
       suffixLen_is_depth = plusLeftCancel prefixLen (length suffixVars) envDepth $ Calc $ 
            |~ prefixLen       + (length suffixVars)
            ~~ length keptVars + (length suffixVars)  ...(cong (+ (length suffixVars))
                                                          $ sym prefixLen_is_len)
            ~~ length(keptVars ++        suffixVars)  ...(sym $ lengthDistributesOverAppend
                                                                keptVars suffixVars)
            ~~ length vars'                           ...(cong length $ sym varsDecomposition)
            ~~ length env'                            ...(sym len_is_len)
            ~~ prefixLen + envDepth                   ...(sym $ plusMinusLte envDepth len d_lte_len)
            
       
       0 envDepth_lte_suffixLen : envDepth `LTE` (length suffixVars)
       envDepth_lte_suffixLen = rewrite suffixLen_is_depth in 
                                reflexive envDepth
       
       liftedEnv : Env Term suffixVars
       liftedEnv = dropEnv prefixLen env'
                           
       0 prefixVars : List Name
       prefixVars = take envDepth suffixVars 
       0 remainder : List Name
       remainder = drop envDepth suffixVars 
                  
       0 prefixVars_is_suffixVars : (prefixVars = suffixVars)
       prefixVars_is_suffixVars = concatRightCancel 
         prefixVars remainder suffixVars [] 
         (Calc $
         |~ length prefixVars
         ~~ envDepth          ...(reflectLength $ snd $ 
                                  specTakeDrop envDepth suffixVars envDepth_lte_suffixLen)
         ~~ length suffixVars ...(sym suffixLen_is_depth))
         (Calc $ 
         |~ prefixVars ++ remainder
         ~~ suffixVars       ...(sym $ fst $ specTakeDrop envDepth suffixVars envDepth_lte_suffixLen)
         ~~ suffixVars ++ [] ...(sym $ appendNilRightNeutral suffixVars))
       
       targetEnv : SubstEnv suffixVars suffixVars
       targetEnv = replace {p = \v => SubstEnv v suffixVars} prefixVars_is_suffixVars $
                   takeEnv envDepth liftedEnv
       
       SizeOfSuffix : SizeOf suffixVars
       SizeOfSuffix = MkSizeOf envDepth $ 
                               replace {p = \n => HasLength n suffixVars} suffixLen_is_depth $
                               mkHasLength suffixVars
       
   in do
   scope <- peel SizeOfSuffix liftedTy 
   (let theta : SizeOf keptVars
        theta = MkSizeOf prefixLen (replace {p = \n => HasLength n keptVars} prefixLen_is_len $
                                            mkHasLength keptVars)
        actualTy : Term vars'
        actualTy = rewrite varsDecomposition in 
                   weakenNs theta
                            scope
        args : List (Term vars')
        args = rewrite varsDecomposition in 
               map (weakenNs theta) $ reverse $ listFromSubstEnv targetEnv
        actualTm : Term vars'
        actualTm = apply fc tm args
    in pure (actualTy, actualTm)))

