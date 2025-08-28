{-# LANGUAGE TemplateHaskell #-}

-- | Template Haskell to derive pattern synonyms for working with demands
module Test.StrictCheck.TH
  ( derivePatternSynonyms,
  )
where

import Control.Monad (when)
import Generics.SOP (NP (..), NS (..))
import Language.Haskell.TH
import Test.StrictCheck.Demand
import Test.StrictCheck.Shaped

-- TODO: generate COMPLETE pragmas to avoid partiality warnings

-- | Generates the proper type signature for a pattern. The first
-- argument is the list of constructor field types, and the second
-- argument is the type of the constructor constructs. This function
-- inserts '->' and 'Demand' at the correct places.
patternTypeDec :: [Type] -> Type -> Type
patternTypeDec [] ty = AppT (ConT ''Demand) ty
patternTypeDec (arg : args) ty =
  AppT
    (AppT ArrowT $ AppT (ConT ''Demand) arg)
    (patternTypeDec args ty)

prefixPatternDec :: Int -> Name -> [Name] -> Pat -> Dec
prefixPatternDec idx patName binderNames npPat =
  PatSynD
    patName
    (PrefixPatSyn binderNames)
    ImplBidir
    (ConP 'Wrap [] [ConP 'Eval [] [ConP 'GS [] [sumPattern idx npPat]]])

infixPatternDec ::
  Int ->
  Name ->
  Name ->
  Name -> -- LHS then RHS
  Pat ->
  Dec
infixPatternDec idx patName lhsBinder rhsBinder npPat =
  PatSynD
    patName
    (InfixPatSyn lhsBinder rhsBinder)
    ImplBidir
    (ConP 'Wrap [] [ConP 'Eval [] [ConP 'GS [] [sumPattern idx npPat]]])

sumPattern :: Int -> Pat -> Pat
sumPattern idx p
  | idx <= 0 = ConP 'Z [] [p]
  | otherwise = ConP 'S [] [sumPattern (idx - 1) p]

productPattern :: [Type] -> Q (Pat, [Name])
productPattern [] = return (ConP 'Nil [] [], [])
productPattern (_ : args) = do
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
  return
    ( PatSynSigD patDecName (patternTypeDec (map snd argTypes) ty),
      prefixPatternDec idx patDecName names npPat
    )
  where
    patDecName = mkName (nameBase conName ++ "'")
constructor2PatternDec ty idx (InfixC argType1 conName argType2) = do
  let argTypes = [argType1, argType2]
  (npPat, names) <- productPattern (map snd argTypes)
  case names of
    nm1 : nm2 : [] ->
      return
        ( PatSynSigD patDecName (patternTypeDec (map snd argTypes) ty),
          infixPatternDec idx patDecName nm1 nm2 npPat
        )
    _ -> fail "The impossible happened: Infix Pattern have more than 2 binders"
  where
    patDecName = mkName (nameBase conName ++ "%")
constructor2PatternDec _ _ _ =
  fail "Test.StrictCheck.TH cannot derive pattern synonyms for fancy types"

-- | Template Haskell splice to generate pattern synonym declarations for
-- working with explicitly-represented demands on a type whose 'Shape' is
-- implemented generically as a 'GShape'
derivePatternSynonyms :: Name -> Q [Dec]
derivePatternSynonyms name = do
  nameInfo <- reify name
  case nameInfo of
    TyConI (DataD _ tyName tyVars _ constrs _) -> do
      let tyVarTypes =
            map
              ( \tyVar -> case tyVar of
                  PlainTV nm _ -> VarT nm
                  KindedTV nm _ kd -> SigT (VarT nm) kd
              )
              tyVars
          ty = foldl AppT (ConT tyName) tyVarTypes
      decs <- mapM (uncurry (constructor2PatternDec ty)) (zip [0 ..] constrs)
      return $ (map fst decs) ++ (map snd decs)
    _ -> do
      reportError (show name ++ " is not a data type name")
      return []
