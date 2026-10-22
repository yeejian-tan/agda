module Agda.TypeChecking.Primitive.Cubical.UIP (
  -- prim_sqPFill', prim_uip',
  prim_sqFill'
  ) where

import Agda.TypeChecking.Monad
-- import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Names
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Primitive.Cubical.Base

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Primitive.Base
import Agda.TypeChecking.Substitute

import Agda.Utils.Impossible
import Agda.TypeChecking.SizedTypes.Utils (debug)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Warnings (warning)
import Agda.TypeChecking.Free (freeIn)
import Agda.Utils.Maybe (isJust, fromJust)
-- import Agda.TypeChecking.Level (LevelKit(lvlZero))

isNonDep :: Term -> Maybe Term
isNonDep (Lam _ b) = isNoAbs b
isNonDep _         = Nothing

-- Only for Type.
prim_sqFill' :: TCM PrimitiveImpl
prim_sqFill' = do
  requireCubical CUip
  t <- runNamesT [] $
       hPi' "l" (el $ cl primLevel) $ \ la ->
       nPi' "A" (sort . tmSort <$> la) $ \ bA ->
       el $ primSqFill <#> la <@> bA

  return $ PrimImpl t $
    -- primfunargoccur is for positivity when my primitive is applied to an inductive type.
    -- try when applying to an inductive type.
    PrimFun __IMPOSSIBLE__ 2 [] $ \ts nelims -> do
      case ts of
        []    -> __IMPOSSIBLE__ -- not enough arguments
        [_lc] -> __IMPOSSIBLE__ -- not enough arguments

        lc:bC:rest -> do
          sbC <- reduceB' bC
          let tbC = unArg $ ignoreBlocking sbC
          mSigma      <- getBuiltinName' builtinSigma
          mUnit       <- getBuiltinName' builtinUnit
          mBool       <- getBuiltinName' builtinBool
          mNat       <- getBuiltinName' builtinNat
          mList       <- getBuiltinName' builtinList
          mMaybe       <- getBuiltinName' builtinMaybe
          mProduct    <- getBuiltinName' builtinProduct
          mCoproduct  <- getBuiltinName' builtinCoproduct
          mpath  <- getBuiltinName' builtinPath
          mpathp <- getBuiltinName' builtinPathP
          let
            tLam = Lam defaultArgInfo

            -- TODO: there are a few more ad-hoc getLevel impls that can be unified
            getLevel :: MonadReduce m => Type -> m Term
            getLevel b = do
              s <- reduce $ getSort b
              case s of
                Type l -> pure (Level l)
                _ -> __IMPOSSIBLE__

          case tbC of

            Pi aDom bAbs -> do
              tmSqFill <- getTerm "for SqFillPi" builtin_sqFill -- recursive!
              sqFillPi <- getTerm "for SqFillPi" builtinSqFillPi
              let bA = pure . unEl $ unDom aDom
                  bB = pure $ Lam defaultArgInfo (unEl <$> bAbs) -- λ a. B a
                  lA = getLevel $ unDom aDom
              lB <- getLevel $ unAbs bAbs
              let bAbsHidden = Arg (setHiding Hidden defaultArgInfo) lB
                  ba = apply tmSqFill [bAbsHidden, defaultArg (unEl $ unAbs bAbs)]
                  sqFillB = pure $ Lam defaultArgInfo $ bAbs {unAbs = ba} -- λ a . primSqFill (B a)
              ret <- pure sqFillPi <#> lA <#> pure lB <@> bA <@> bB <@> sqFillB
              redReturn $ ret `apply` rest

            -- Sigma
            Def q [Apply la, Apply lb, Apply bA, Apply bB] | Just q == mSigma -> do
              tmSqFill <- getTerm "for SqFillSigma" builtin_sqFill -- recursive!
              sqFillSigma <- getTerm "for SqFillSigma" builtinSqFillSigma

              bB <- unArg <$> reduce bB
              let sqFillA = apply tmSqFill [la, bA]
              sqFillB <- runNamesT [] $ do
                          let sf = cl' tmSqFill
                              bB' = cl' bB
                          lam "a" $ \ a -> sf <#> pure (unArg lb) <@> (bB' <@> a)
              let ret = apply sqFillSigma [la, lb, bA, defaultArg sqFillA, defaultArg bB, defaultArg sqFillB]
              redReturn $ ret `apply` rest

            -- TODO: pdt and copdt can be unified in impl
            -- Product
            Def q [Apply la, Apply lb, Apply bA, Apply bB] | Just q == mProduct -> do
              tmSqFill      <- getTerm "for SqFillProduct" builtin_sqFill -- recursive!
              sqFillProduct <- getTerm "for SqFillProduct" builtinSqFillProduct
              let sqFillA = apply tmSqFill [la, bA]
                  sqFillB = apply tmSqFill [lb, bB]
                  ret = apply sqFillProduct [la, lb, bA, defaultArg sqFillA, bB, defaultArg sqFillB]
              redReturn $ ret `apply` rest

            -- Coproduct
            Def q [Apply la, Apply lb, Apply bA, Apply bB] | Just q == mCoproduct -> do
              tmSqFill    <- getTerm "for SqFillCoproduct" builtin_sqFill -- recursive!
              sqFillCoproduct <- getTerm "for SqFillCoproduct" builtinSqFillCoproduct
              let sqFillA = apply tmSqFill [la, bA]
                  sqFillB = apply tmSqFill [lb, bB]
                  ret = apply sqFillCoproduct [la, lb, bA, defaultArg sqFillA, bB, defaultArg sqFillB]
              redReturn $ ret `apply` rest

            Def q []
              | Just q == mUnit -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting Unit type" <+> prettyTCM tbC
                sqFillUnit <- getTerm "for SqFillUnit" builtinSqFillUnit
                redReturn $ sqFillUnit `apply` rest

              | Just q == mBool -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting Bool type" <+> prettyTCM tbC
                sqFillBool <- getTerm "for SqFillBool" builtinSqFillBool
                redReturn $ sqFillBool `apply` rest

              | Just q == mNat -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting Nat type" <+> prettyTCM tbC
                sqFillNat <- getTerm "for SqFillNat" builtinSqFillNat
                redReturn $ sqFillNat `apply` rest

            -- List
            -- YJ : the required signature for list is @Set -> Set@, and can be prefixed by any number of implicit
            -- arguments that can probably (CHECK) only be levels, so @{l} -> Set l -> Set l@ and
            -- @{a b} -> Set a -> Set (lmax a b)@ etc are accepted.
            -- Instead of getting level from any hidden argument, we use the constraint that the domain and codomain
            -- must have the same level and take the level from the parameter @A : Type@ of the list.
            -- [TODO] 1. find the first explicit argument 2. extract the level from it 
            Def q [Apply la, Apply bA]
              | Just q == mList -> do
                  reportSDoc "cubical.prim.uip" 40 $ "we are getting List type" <+> prettyTCM tbC
                  tmSqFill    <- getTerm "for SqFillList" builtin_sqFill -- recursive!
                  sqFillList <- getTerm "for SqFillList" builtinSqFillList
                  let sqFillA = apply tmSqFill [la, bA]
                  redReturn $ apply sqFillList ([la, bA, defaultArg sqFillA] ++ rest)

            -- [TODO] YJ: Same applies for Maybe.
            Def q [Apply la, Apply bA]
              | Just q == mMaybe -> do
                  reportSDoc "cubical.prim.uip" 40 $ "we are getting Maybe type" <+> prettyTCM tbC
                  tmSqFill    <- getTerm "for SqFillList" builtin_sqFill -- recursive!
                  sqFillMaybe <- getTerm "for SqFillMaybe" builtinSqFillMaybe
                  let sqFillA = apply tmSqFill [la, bA]
                  redReturn $ apply sqFillMaybe ([la, bA, defaultArg sqFillA] ++ rest)

            -- Note: reducing bC always unfolds _≡_ to PathP, so the Just path' == mpath
            -- guard is never fired in practice; the isNonDep check handles non-dep paths.
            Def path' [Apply l, Apply bP, Apply x, Apply y]
              | Just path' == mpath || isJust (isNonDep (unArg bP)) -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting path type" <+> prettyTCM tbC
                tmSqFill    <- getTerm "for SqFillPath" builtin_sqFill -- recursive!
                sqFillPath <- getTerm "for SqFillPath" builtinSqFillPath
                iZero <- getTerm "for SqFillPathP" builtinIZero
                let
                  bA = (unArg bP) `apply` [defaultArg iZero]
                  sqFillA :: Term = apply tmSqFill [l, defaultArg bA]
                redReturn $ sqFillPath `apply` [l, defaultArg bA, x, y, defaultArg sqFillA]

              | Just path' == mpathp -> do
                reportSDoc "cubical.prim.uip" 40 $ "we are getting pathp type" <+> prettyTCM tbC
                tmSqFill    <- getTerm "for SqFillPathP" builtin_sqFill -- recursive!
                sqFillPathP <- getTerm "for SqFillPathP" builtinSqFillPathP
                iOne <- getTerm "for SqFillPathP" builtinIOne
                iZero <- getTerm "for SqFillPathP" builtinIZero
                let
                  bA = (unArg bP) `apply` [defaultArg iZero]
                  bB = (unArg bP) `apply` [defaultArg iOne]
                  sqFillA :: Term = apply tmSqFill [l, defaultArg bA]
                redReturn $ sqFillPathP `apply` [l, defaultArg bA, defaultArg bB, x, y, bP, defaultArg sqFillA]

            -- Records
            -- Processing a record type as a nested sigma type:
            -- 1. given Record type R, translate its telescope to a sigma type.
            --    HS[TelToSigma : Telescope -> Term]
            -- 2. apply sqFill on the Sigma type and we get a term 
            --    Agda[surrogate : Square (TeltoSigma R) -> I -> I -> (TeltoSigma R)]
            -- 3. we return a term 
            --    [Square R -> I -> I -> R] defined as
            --    λ l r u d    i    j    .elim -> surrogate (nest l) .. (nest d) i j .(elimToProj)
            --    where 
            --      Agda[nest : Term -> Term]
            Def q es -> do
              reportSDoc "cubical.prim.uip" 40 $ "we have a record" <+> prettyTCM tbC
              let 
                -- Input: A telescope list (usually by [telToList $ telFields R]) of a record type R
                -- Output: 
                --    Its corresponding left-assoc sigma type. 
                -- eg: [Record {A B C} -> Σ (Σ A B) C]
                telListToSigma :: (MonadTCError m, HasBuiltins m) => [Dom (ArgName, Term)] -> m Term
                telListToSigma [] = __IMPOSSIBLE__ -- [TODO] YJ: empty record, isom to unit
                telListToSigma (a:rest) = 
                  foldl (\acc ty -> primSigma <@> acc <@> (pure $ snd $ unDom ty)) 
                        (pure $ snd $ unDom a) rest

                -- Input: 
                --    a record of type R 
                -- Output: 
                --    its nested pair representation (left-assoc), of type [telListToSigma (telToList $ telFields R)
                -- Eg: recordCon {a b c} -> ((a, b) , c)
                nest :: (MonadTCError m, HasBuiltins m) 
                  => [QName] -- fields
                  -> Term  -- record term
                  -> m Term  -- sigma term
                nest fields r = do
                  let primPair = getBuiltin BuiltinSigmaCon
                      proj :: QName -> Term
                      proj fieldName = applyE r [(Proj ProjSystem fieldName)]

                  case map (pure . proj) fields of
                    [] -> __IMPOSSIBLE__ -- [TODO] 
                    hd:tl -> foldl (\acc field -> primPair <@> acc <@> field) hd tl

                -- essentially [cong nest := λ p i → nest (p i)], 
                --  taking a path of records to a path of sigmas
                nestPath :: (MonadTCError m, HasBuiltins m) => [QName] -> Term -> m Term
                nestPath fields recordPath = runNamesT [] $ do 
                  lam "i" $ \i -> do 
                    p' <- open recordPath
                    body <- p' <@> i
                    ret <- nest fields body
                    return ret

              info <- getConstInfo q
              let
                -- Let's just address the bare minimum: 
                -- noeta, copattern matching records, applied to eliminator.
                isCopatternRecord r@Record{recEtaEquality' = eta} = case theEtaEquality eta of
                  NoEta PatternMatching -> False
                  _ -> True
                isCopatternRecord _ = False

              case theDef info of
                -- tel = params ++ telFields
                r@Record{recFields = fields, recTel = tel} | isCopatternRecord r -> do
                  -- isNoEtaRecord r, Just as <- allApplyElims es -> -- [TODO] do we need to apply elim?
                  reportSDoc "cubical.prim.uip" 40 $ "we have a record" <+> prettyTCM tbC
                  reportSDoc "cubical.prim.uip" 40 $ "there are" <+> prettyTCM (length fields) <+> "fields"
                  reportSDoc "cubical.prim.uip" 40 $ "the fields are" <+> prettyTCM (map unDom fields)
                  reportSDoc "cubical.prim.uip" 40 $ "the tel is" <+> prettyTCM tel
                  let telList = map unDom (telToList tel)
                  reportSDoc "cubical.prim.uip" 40 $ "the telList has length" <+> prettyTCM (length telList)
                  reportSDoc "cubical.prim.uip" 40 $ "the telList is" <+> prettyTCM telList
                  nored lc sbC

                r@Record{recEtaEquality' = eta} -> do
                  reportSDoc "cubical.prim.uip" 40 $ pshow eta
                  nored lc sbC
                  
                _ -> do
                  reportSDoc "cubical.prim.uip" 40 $ "we are getting unmatched def type" <+> prettyTCM tbC
                  reportSDoc "cubical.prim.uip" 40 $ "the qname is" <+> prettyTCM q
                  nored lc sbC

            -- FIXME: sort will fall here!
            Sort _ -> do
              nored lc sbC

            --
            t -> do
              reportSDoc "cubical.prim.uip" 40 $ "we are getting type" <+> prettyTCM tbC
              reportSDoc "cubical.prim.uip" 60 $ "internal representation:" <+> pretty tbC
              nored lc sbC

      where
        -- Must return all arity (= 2) arguments, see reducePrimitive.
        nored lc sbC = return $ NoReduction [notReduced lc, reduced sbC]


-- -- Only for Type.
-- prim_sqPFill' :: TCM PrimitiveImpl
-- prim_sqPFill' = do
--   requireCubical CUip
--   t <-  runNamesT [] $
--         nPi' "A" (primIntervalType --> primIntervalType --> tset) $ \ bA ->
--         let tySqPFill = getTerm "for SqPFill" builtinSqPFill in
--         el $ tySqPFill <@> bA

--   return $ PrimImpl t $
--     PrimFun __IMPOSSIBLE__ 9 [] $ \ts _nelims -> do
--       case ts of
--         bC:rest -> do
--           reportSDoc "cubical.prim.uip" 30 $ (text "reducing type") <+> prettyTCM bC
--           sbC <- reduceB' bC
--           reportSDoc "cubical.prim.uip" 30 $ (text "reduced type") <+> prettyTCM sbC
--           case unArg $ ignoreBlocking sbC of
--             Pi aDom bAbs -> do
--               reportSDoc "cubical.prim.uip" 20 "we are in SqPFillPi"
--               tySqPFill <- getTerm "for SqPFillPi" builtinSqPFill
--               sqPFillPi <- getTerm "for SqPFillPi" builtinSqPFillPi
--               -- A -> B -> SqPFill B -> SqPFill (A -> B), but dependent
--               let bA = pure $ unEl (unDom aDom)
--               let bB = pure $ unEl (unAbs bAbs)
--               let sqPFillB = pure tySqPFill <@> bB
--               -- ret <- pure sqPFillPi <@> bA <@> bB <@> sqPFillB
--               ret <- foldl (<@>) (pure sqPFillPi) ([bA, bB, sqPFillB] ++ map (pure . unArg) rest)
--               redReturn ret
--             -- Lam arginfo (NoAbs {unAbs = (Lam arginfo' (NoAbs {unAbs = t}))}) -> do
--             t@(Lam _ _) -> do
--               reportSDoc "cubical.prim.uip" 20 $ text (show t)
--               nored
--             _ -> nored
--         [] -> nored
--       where
--         nored = return $ NoReduction []

-- prim_uip' :: TCM PrimitiveImpl
-- prim_uip' = do
--   requireCubical CUip
--   t <-  runNamesT [] $
--         hPi' "a" (els (pure LevelUniv) (cl primLevel)) $ \ la ->
--         hPi' "A" (sort . tmSort <$> la) $ \ bA ->
--         nPi' "x" (el' la bA) $ \ x ->
--         nPi' "y" (el' la bA) $ \ y ->
--         let pathxy = cl primPath <#> la <#> bA <@> x <@> y in
--         nPi' "p" (el' la $ pathxy) $ \ p ->
--         nPi' "q" (el' la $ pathxy) $ \ q ->
--         el' la $ cl primPath <#> la <#> pathxy <@> p <@> q
--   return $ PrimImpl t $
--     PrimFun __IMPOSSIBLE__ 6 [] $ \ts _nelims ->
--       return $ NoReduction []

-- ifThenElse :: HasBuiltins m => m Term
-- ifThenElse = runNamesT [] $ do
--   lam "i" $ \ i ->
--     lam "j" $ \ j ->
--     lam "k" $ \ k -> (imax (imin k (imax (ineg i) j)) (imin j (imax i k)))

-- transport :: HasBuiltins m => m Term -> m Term -> m Term -> m Term
-- transport l p a = do
--   tTrans <- getTerm "transp for UIP" builtinTrans
--   iz     <- getTerm "izero for UIP" builtinIZero
--   return tTrans <#> l <@> p <@> return iz <@> a

-- -- spread : (i j : I) → (a : A i j) → (i' j' : I) → A i' j'
-- -- This is done by "transport"-ing a,
-- -- since we could not state the transp cofibration when (i = i' ∧ j = j').
-- spread :: HasBuiltins m => m Term
-- spread = runNamesT [] $ do
--   lam "lA"   $ \ lA ->
--     lam "bA" $ \ bA ->
--     lam "i"  $ \ i ->
--     lam "j"  $ \ j ->
--     lam "a"  $ \ a ->
--     lam "i'" $ \ i' ->
--     lam "j'" $ \ j' -> do
--       let
--         iCoe k = ifThenElse <@> k <@> i <@> i'
--         jCoe k = ifThenElse <@> k <@> j <@> j'
--       transport lA (lam "k" \k -> bA <@> iCoe k <@> jCoe k) a

-- -- transportFiller : {l A B} (p : A ≡ B) → (a : A) → a ≡ transport p a
-- -- transportFiller p a i = transp (λ j → p (i ∧ j)) (~ i) a
-- transportFiller :: HasBuiltins m => m Term
-- transportFiller = runNamesT [] $ do
--   lam "lA" $ \lA ->
--     lam "bA" $ \bA ->
--     lam "bB" $ \bB ->
--     lam "p"  $ \p ->
--     lam "a"  $ \a ->
--     lam "i"  $ \i -> do
--       tTrans <- getTerm "transp for UIP" builtinTrans
--       return tTrans <#> lA <@> (lam "j" \j -> p <@> (imin i j)) <@> ineg i <@> a

-- -- ≡spread : (i j : I) (a : A i j) → a ≡ spread i j a i j
-- -- ≡spread i j a = transport-filler (λ k → A (if k then i else i end) (if k then j else j end)) a
-- spreadFill :: HasBuiltins m => m Term
-- spreadFill = runNamesT [] $ do
--   lam "lA" $ \lA ->
--     lam "bA" $ \bA ->
--     lam "i" $ \i ->
--     lam "j" $ \j ->
--     lam "a" $ \a ->
--     lam "i'" $ \i' ->
--     lam "j'" $ \j' -> do
--       let
--         iCoe k = ifThenElse <@> k <@> i <@> i'
--         jCoe k = ifThenElse <@> k <@> j <@> j'
--       transportFiller <#> lA <@> (lam "k" \k -> bA <@> iCoe k <@> jCoe k) <@> a
--   lam "lA" $ \lA ->
--     lam "bA" $ \bA ->
--     lam "i" $ \i ->
--     lam "j" $ \j ->
--     lam "a" $ \a ->
--     lam "i'" $ \i' ->
--     lam "j'" $ \j' -> do
--       let
--         iCoe k = ifThenElse <@> k <@> i <@> i'
--         jCoe k = ifThenElse <@> k <@> j <@> j'
--       transportFiller <#> lA <@> (lam "k" \k -> bA <@> iCoe k <@> jCoe k) <@> a
