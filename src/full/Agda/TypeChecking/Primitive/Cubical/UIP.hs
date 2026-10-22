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
import Agda.Utils.Maybe (isJust)
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
        []  -> __IMPOSSIBLE__ -- not enough arguments
        [_] -> __IMPOSSIBLE__ -- not enough arguments

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

            -- TODO: pdt and copdt can be unified in impl
            -- Product
            -- Note: reducing bC always unfolds _×_ to Σ A (λ _ → B), so the Just q == mProduct
            -- guard is never fired in practice; the isNonDep check handles non-dep sigmas.
            Def q [Apply la, Apply lb, Apply bA, Apply bB']
              | Just q == mProduct || (Just q == mSigma && isJust (isNonDep (unArg bB'))) -> do
              tmSqFill      <- getTerm "for SqFillProduct" builtin_sqFill -- recursive!
              sqFillProduct <- getTerm "for SqFillProduct" builtinSqFillProduct
              let bB = maybe bB' (<$ bB') (isNonDep (unArg bB'))
                  sqFillA = apply tmSqFill [la, bA]
                  sqFillB = apply tmSqFill [lb, bB]
                  ret = apply sqFillProduct [la, lb, bA, defaultArg sqFillA, bB, defaultArg sqFillB]
              redReturn $ ret `apply` rest

            -- Sigma
            Def q [Apply la, Apply lb, Apply bA, Apply bB] | Just q == mSigma -> do
              tmSqFill <- getTerm "for SqFillSigma" builtin_sqFill -- recursive!
              sqFillSigma <- getTerm "for SqFillSigma" builtinSqFillSigma
              let sqFillA = apply tmSqFill [la, bA]
              sqFillB <- runNamesT [] $ do
                lb' <- open (unArg lb)
                bB' <- open (unArg bB)
                lam "a" \a -> pure tmSqFill <#> lb' <@> (bB' <@> a) -- λ a . primSqFill (B a)
              getContextTelescope >>= \t -> reportSDoc "cubical.prim.uip" 40 $ "context is" <+> prettyTCM t
              let ret = apply sqFillSigma [la, lb, bA, defaultArg sqFillA, bB, defaultArg sqFillB]
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
              info <- getConstInfo q
              case theDef info of
                -- tel = params ++ telFields
                Record{recFields = fields, recTel = tel, recEtaEquality' = eta, recConHead = conR}
                  -- [TODO] think about pattern matching records
                  | not (NoEta PatternMatching == theEtaEquality eta), Just as <- allApplyElims es -> do
                    -- recTel includes the parameters, instantiate them to get the field telescope.
                    let fieldDoms = telToList $ tel `apply` as
                    -- the constructor and projections of Σ, for nesting and for referring to
                    -- earlier fields in the nested sigma
                    mSigmaProjs <- case mSigma of
                      Nothing -> pure Nothing
                      Just sigma -> theDef <$> getConstInfo sigma >>= \case
                        Record{recConHead = pair, recFields = [pfst, psnd]} ->
                          pure $ Just (sigma, pair, unDom pfst, unDom psnd)
                        _ -> __IMPOSSIBLE__
                    case mSigmaProjs of
                      Nothing -> nored lc sbC -- the SIGMA builtin is not bound
                      Just (sigma, pair, pfst, psnd) -> do
                        -- [TODO] irrelevant fields cannot be nested into a Σ
                        mSigmaRecord <- if all isRelevant fieldDoms
                          then telToSigma sigma pfst psnd $ map (snd . unDom) fieldDoms
                          else pure Nothing
                        let
                          -- Without eta, @unnest (nest x)@ is not definitionally @x@, so the boundary
                          -- of the square only holds after projecting: only reduce when the square
                          -- is fully applied (to the 10 arguments of SqFill R) and then projected.
                          canReduce = case theEtaEquality eta of
                            YesEta                 -> True
                            NoEta CopatternMatching -> nelims > 10
                            NoEta PatternMatching   -> False

                          -- Input: a record of type R
                          -- Output: its nested pair repr. (left-assoc), of type [telToSigma R]
                          -- Eg: recordCon {a b c} -> ((a, b) , c)
                          nest :: Term -> Term
                          nest x = foldl1 (\acc y -> Con pair ConOSystem [Apply (defaultArg acc), Apply (defaultArg y)])
                            [ x `applyE` [Proj ProjSystem (unDom f)] | f <- fields ]

                          -- Inverse of nest: a nested pair of type [telToSigma R] to a record of type R
                          -- Eg: ((a, b) , c) -> recordCon {a b c}
                          unnest :: Term -> Term
                          unnest s = Con conR ConOSystem
                            [ Apply (v <$ argFromDom d) | (d, v) <- zip fieldDoms (sigmaProjs pfst psnd (length fieldDoms) s) ]

                        case mSigmaRecord of
                          Just (sigmaRecord, lSigma) | canReduce -> do
                            -- 2. get sqfill on it
                            tmSqFill <- getTerm "for SqFillRecord" builtin_sqFill -- recursive!
                            let surrogate = apply tmSqFill [hide $ defaultArg (Level lSigma), defaultArg sigmaRecord]
                            reportSDoc "cubical.prim.uip" 40 $ "the nested sigma is" <+> prettyTCM sigmaRecord
                            reportSDoc "cubical.prim.uip" 40 $ "the surrogate is" <+> prettyTCM surrogate
                            -- 3. transport the square along R ≅ telToSigma R:
                            --    λ {a₀₀ a₀₁} a₀₋ {a₁₀ a₁₁} a₁₋ a₋₀ a₋₁ i j →
                            --      unnest (surrogate {nest a₀₀} {nest a₀₁} (λ k → nest (a₀₋ k)) … i j)
                            ret <- runNamesT [] $ do
                              sur <- open surrogate
                              let hlam = glam (setHiding Hidden defaultArgInfo)
                                  nestM = fmap nest
                                  -- [cong nest p], taking a path of records to a path of sigmas
                                  nestP p x y = lam "k" \k -> nestM (p <@@> (x, y, k))
                              hlam "a₀₀" \a00 -> hlam "a₀₁" \a01 -> lam "a₀₋" \l ->
                                hlam "a₁₀" \a10 -> hlam "a₁₁" \a11 -> lam "a₁₋" \r ->
                                lam "a₋₀" \u -> lam "a₋₁" \d -> lam "i" \i -> lam "j" \j ->
                                unnest <$> (sur <#> nestM a00 <#> nestM a01 <@> nestP l a00 a01
                                                <#> nestM a10 <#> nestM a11 <@> nestP r a10 a11
                                                <@> nestP u a00 a10 <@> nestP d a01 a11 <@> i <@> j)
                            reportSDoc "cubical.prim.uip" 40 $ "the record square is" <+> prettyTCM ret
                            redReturn $ ret `apply` rest
                          _ -> nored lc sbC
                    where
                      -- Input: the field types of a record type R (parameters applied), where the
                      --    k-th field type lives in the context extended with the k earlier fields.
                      -- Output: Its corresponding left-assoc sigma type and its level, or Nothing if
                      --    a field is not in @Type ℓ@ or its level depends on earlier fields.
                      -- eg: [Record {a : A; b : B a; c : C a b} -> Σ (Σ A (λ p → B p)) (λ p → C (fst p) (snd p))]
                      telToSigma :: QName -> QName -> QName -> [Type] -> ReduceM (Maybe (Term, Level))
                      telToSigma _ _ _ [] = pure Nothing -- [TODO] YJ: empty record, isom to unit
                      telToSigma sigma pfst psnd (t0 : ts) = fieldLevel 0 t0 >>= \case
                        Nothing -> pure Nothing
                        Just l0 -> go 1 (unEl t0) l0 ts
                        where
                          -- @acc : Type lAcc@ is the nested sigma of the first k fields
                          go :: Int -> Term -> Level -> [Type] -> ReduceM (Maybe (Term, Level))
                          go _ acc lAcc [] = pure $ Just (acc, lAcc)
                          go k acc lAcc (t : ts') = fieldLevel k t >>= \case
                            Nothing -> pure Nothing
                            Just l -> do
                              let -- Γ, p ⊢ σ : Γ, x₀ … xₖ₋₁, replacing the earlier fields by projections of p
                                  σ    = foldr (:#) (raiseS 1) $ reverse $ sigmaProjs pfst psnd k (var 0)
                                  bB   = Lam defaultArgInfo $ Abs "p" $ applySubst σ (unEl t)
                                  acc' = Def sigma $ map Apply
                                    [ hide $ defaultArg (Level lAcc), hide $ defaultArg (Level l)
                                    , defaultArg acc, defaultArg bB ]
                              go (k + 1) acc' (levelLub lAcc l) ts'

                      -- the k fields x₀ … xₖ₋₁ of p : Σ (… (Σ X₀ X₁) …) Xₖ₋₁
                      sigmaProjs :: QName -> QName -> Int -> Term -> [Term]
                      sigmaProjs pfst psnd k p
                        | k <= 1    = [p]
                        | otherwise = sigmaProjs pfst psnd (k - 1) (p `applyE` [Proj ProjSystem pfst])
                                      ++ [p `applyE` [Proj ProjSystem psnd]]

                      -- the level of the k-th field type, strengthened past the k earlier fields
                      fieldLevel :: Int -> Type -> ReduceM (Maybe Level)
                      fieldLevel k t = reduce (getSort t) >>= \case
                        Type l | not (any (`freeIn` l) [0 .. k - 1]) ->
                          pure $ Just $ applySubst (strengthenS impossible k) l
                        _ -> pure Nothing


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
