{-# LANGUAGE TemplateHaskell #-}

module Test.StrictCheck.TH where

import Generics.SOP (NP(..), NS(..), SOP(..), I(..), Rep)
import Language.Haskell.TH

-- | Turns a constructor into its corresponding pattern synonym
-- declaration. The `Int` argument is the index of the constructor.
-- For example, Nil would be the 0th constructor, and Cons would be
-- the 1st constructor of the type data List a = Nil | Cons a (List a).
constructor2PatternDec :: Type -> Int -> Con -> Q (Dec, Dec)
constructor2PatternDec ty idx (NormalC conName argTypes) = do
  runIO $ mapM_ print argTypes
  (npPat, names) <- prodPat argTypes
  return (PatSynSigD patDecName (patTyDec argTypes),
          patDec npPat names)
  where patTyDec []         = AppT (ConT ''Rep) ty
        patTyDec (arg:args) = AppT (AppT ArrowT (snd arg)) (patTyDec args)

        patDec npPat names =
          PatSynD patDecName
                  (PrefixPatSyn names)
                  Unidir
                  (ConP 'SOP [sumPat idx npPat])
                   
        sumPat :: Int -> Pat -> Pat
        sumPat i p | i <= 0    = ConP 'Z [p]
                   | otherwise = ConP 'S [sumPat (i-1) p]

        prodPat :: [(Bang, Type)] -> Q (Pat, [Name])
        prodPat []       = return (ConP 'Nil [], [])
        prodPat (_:args) = do
          (tailPat, names) <- prodPat args
          freshName <- newName "x"
          return $ (InfixP (ConP 'I [VarP freshName]) ('(:*)) tailPat,
                    freshName : names)

        patDecName = mkName (nameBase conName ++ "'")

derivePatternSynonyms :: Name -> Q [Dec]
derivePatternSynonyms name = do
  nameInfo <- reify name
  runIO $ print nameInfo
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
