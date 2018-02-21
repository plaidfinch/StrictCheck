{-# LANGUAGE TemplateHaskell #-}

module Test.StrictCheck.TH where

import Generics.SOP (NP(..), NS(..), SOP(..), I(..), Rep)
import Test.StrictCheck.Observe
import Test.StrictCheck.Shaped

import Control.Monad (when)
import Language.Haskell.TH

-- | Generates the proper type signature for a pattern. The first
-- argument is the list of constructor field types, and the second
-- argument is the type of the constructor constructs. This function
-- inserts '->' and 'Demand' at the correct places.
patternTypeDec :: [Type] -> Type -> Type
patternTypeDec []         ty = AppT (ConT ''Demand) ty
patternTypeDec (arg:args) ty = AppT (AppT ArrowT $ AppT (ConT ''Demand) arg)
                                    (patternTypeDec args ty)

prefixPatternDec :: Int -> Name -> [Name] -> Pat -> Dec
prefixPatternDec idx patName binderNames npPat =
  PatSynD patName
          (PrefixPatSyn binderNames)
          ImplBidir
          (ConP 'Wrap [ConP 'E [ConP 'GD [sumPattern idx npPat]]])

infixPatternDec :: Int
                -> Name
                -> Name -> Name -- LHS then RHS
                -> Pat
                -> Dec
infixPatternDec idx patName lhsBinder rhsBinder npPat =
  PatSynD patName
          (InfixPatSyn lhsBinder rhsBinder)
          ImplBidir
          (ConP 'Wrap [ConP 'E [ConP 'GD [sumPattern idx npPat]]])

sumPattern :: Int -> Pat -> Pat
sumPattern idx p | idx <= 0  = ConP 'Z [p]
                 | otherwise = ConP 'S [sumPattern (idx-1) p]

productPattern :: [Type] -> Q (Pat, [Name])
productPattern []       = return (ConP 'Nil [], [])
productPattern (_:args) = do
  (tailPat, names) <- productPattern args
  freshName <- newName "x"
  return (InfixP (VarP freshName) '(:*) tailPat, freshName : names)

-- | Turns a constructor into its corresponding pattern synonym
-- declaration. The `Int` argument is the index of the constructor.
-- For example, Nil would be the 0th constructor, and Cons would be
-- the 1st constructor of the type data List a = Nil | Cons a (List a).
constructor2PatternDec :: Type -> Int -> Con -> Q (Dec, Dec)
constructor2PatternDec ty idx (NormalC conName argTypes) = do
  (npPat, names) <- productPattern (map snd argTypes)
  return (PatSynSigD patDecName (patternTypeDec (map snd argTypes) ty),
          prefixPatternDec idx patDecName names npPat)
  where patDecName = mkName (nameBase conName ++ "'")
constructor2PatternDec ty idx (InfixC argType1 conName argType2) = do
  let argTypes = [argType1, argType2]
  (npPat, names) <- productPattern (map snd argTypes)
  when (length names /= 2) $
    reportError "The impossible happened: Infix Pattern have more than 2 binders"
  let nm1:nm2:_ = names
  return (PatSynSigD patDecName (patternTypeDec (map snd argTypes) ty),
          infixPatternDec idx patDecName nm1 nm2 npPat)
  where patDecName = mkName (nameBase conName ++ "%")
constructor2PatternDec _ _ _ =
  fail "Test.StrictCheck.TH cannot derive pattern synonyms for fancy types"

derivePatternSynonyms :: Name -> Q [Dec]
derivePatternSynonyms name = do
  nameInfo <- reify name
  case nameInfo of
    TyConI (DataD _ tyName tyVars _ constrs _) -> do
      let tyVarTypes = map (\tyVar -> case tyVar of
                               PlainTV nm -> VarT nm
                               KindedTV nm kd -> SigT (VarT nm) kd
                           )
                           tyVars
          ty = foldl AppT (ConT tyName) tyVarTypes
      decs <- mapM (uncurry (constructor2PatternDec ty)) (zip [0..] constrs)
      return $ (map fst decs) ++ (map snd decs)
    _ -> do
      reportError (show name ++ " is not a data type name")
      return []
