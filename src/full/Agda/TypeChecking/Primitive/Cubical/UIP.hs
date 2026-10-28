module Agda.TypeChecking.Primitive.Cubical.UIP (
  -- prim_sqPFill', prim_uip',
  prim_sqFill', prim_sqFillData'
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
import Agda.TypeChecking.Free (Free, freeIn)
import Agda.TypeChecking.Telescope (telView)
import Agda.Utils.Maybe (isJust)
import Agda.Utils.Functor ((<&>))
import Agda.Utils.Size (size)
-- import Agda.TypeChecking.Level (LevelKit(lvlZero))

isNonDep :: Term -> Maybe Term
isNonDep (Lam _ b) = isNoAbs b
isNonDep _         = Nothing

-- | The name, constructor and projections of the SIGMA builtin, if bound, for nesting and for
--   referring to earlier fields in a nested sigma.
sigmaKit :: ReduceM (Maybe (QName, ConHead, QName, QName))
sigmaKit = fmap (\k -> (sigmaName k, sigmaCon k, sigmaFst k, sigmaSnd k)) <$> getSigmaKit

-- | Input: the field types of a record type R (parameters applied), or the argument types of a
--      constructor, where the k-th type lives in the context extended with the k earlier ones.
--   Output: Its corresponding left-assoc sigma type and its level, or Nothing if
--      a field is not in @Type ℓ@ or its level depends on earlier fields.
--   eg: [Record {a : A; b : B a; c : C a b} -> Σ (Σ A (λ p → B p)) (λ p → C (fst p) (snd p))]
telListToSigma :: QName -> QName -> QName -> [Type] -> ReduceM (Maybe (Term, Level))
-- empty records with eta and nullary constructors are handled separately
telListToSigma _ _ _ [] = pure Nothing
telListToSigma sigma pfst psnd (t0 : ts) = fieldLevel 0 t0 >>= \case
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

-- | The k fields x₀ … xₖ₋₁ of p : Σ (… (Σ X₀ X₁) …) Xₖ₋₁
sigmaProjs :: QName -> QName -> Int -> Term -> [Term]
sigmaProjs pfst psnd k p
  | k <= 1    = [p]
  | otherwise = sigmaProjs pfst psnd (k - 1) (p `applyE` [Proj ProjSystem pfst])
                ++ [p `applyE` [Proj ProjSystem psnd]]

-- | The level of the k-th field type, strengthened past the k earlier fields.
fieldLevel :: Int -> Type -> ReduceM (Maybe Level)
fieldLevel k t = reduce (getSort t) >>= \case
  Type l | not (any (`freeIn` l) [0 .. k - 1]) ->
    pure $ Just $ applySubst (strengthenS impossible k) l
  _ -> pure Nothing

-- | The edge @e : x ≡ y@ at a generic point k, in weak head normal form.
edgeBody :: (Term, Term, Term) -> ReduceM (Abs Term)
edgeBody (x, y, e) = reduce $ Abs "k" $ raise 1 e `applyE` [IApply (raise 1 x) (raise 1 y) (var 0)]

-- | The constructor heading the edge @e : x ≡ y@ at a generic point k, with its arguments
--   under k, if the edge is constructor-headed.
edgeCon :: (Term, Term, Term) -> ReduceM (Maybe (ConHead, Abs [Arg Term]))
edgeCon e = edgeBody e <&> \case
  Abs k (Con c _ es) | Just args <- properApplies es -> Just (c, Abs k args)
  _ -> Nothing

-- | The arguments of a spine of applications, if there are only (non-path) applications.
properApplies :: Elims -> Maybe [Arg Term]
properApplies = mapM \case
  Apply a -> Just a
  _       -> Nothing

-- | Strengthen a term under the edge variable k (de Bruijn index 0) out of it, if it does not
--   depend on k.
constAlongEdge :: (Free a, Subst a, SubstArg a ~ Term) => a -> Maybe a
constAlongEdge a
  | 0 `freeIn` a = Nothing
  | otherwise    = Just $ applySubst (strengthenS impossible 1) a

-- | Fill a square whose four edges are all of the form @λ k → h (args k)@ for the same head h,
--   given the telescope of the arguments (each in the context of the earlier ones) and how to
--   rebuild a point from its arguments under n more binders (the rebuilding function has to
--   raise the terms it captures by n). The arguments are packed into their nested Σ, filled
--   there by prim^sqFill and unpacked again:
--      λ i j → rebuild (unnest (sqFill (telToSigma args) (λ k → nest (args (a₀₋ k))) … i j))
--   The boundary holds definitionally, e.g. at i0: rebuild (args (a₀₋ j)) = a₀₋ j.
--   Nothing if the arguments cannot be packed into a Σ.
fillVia :: [Dom (ArgName, Type)] -> (Int -> [Arg Term] -> Term)
        -> Abs [Arg Term] -> Abs [Arg Term] -> Abs [Arg Term] -> Abs [Arg Term]
        -> ReduceM (Maybe Term)
fillVia doms rebuild argsL argsR argsU argsD
  -- no arguments: the constant square
  | null doms = Just <$> runNamesT [] (lam "i" \_ -> lam "j" \_ -> pure $ rebuild 2 [])
  -- [TODO] irrelevant arguments cannot be nested into a Σ
  | not (all isRelevant doms) = pure Nothing
  | otherwise = sigmaKit >>= \case
    Nothing -> pure Nothing -- the SIGMA builtin is not bound
    Just (sigma, pair, pfst, psnd) ->
      telListToSigma sigma pfst psnd (map (snd . unDom) doms) >>= \case
        Nothing -> pure Nothing
        Just (sigmaT, lSigma) -> do
          tmSqFill <- getTerm "for SqFillData" builtin_sqFill -- recursive!
          iZ <- getTerm "for SqFillData" builtinIZero
          iO <- getTerm "for SqFillData" builtinIOne
          let
            -- the arguments as a nested pair
            nest :: [Arg Term] -> Term
            nest = foldl1 (\acc y -> Con pair ConOSystem [Apply (defaultArg acc), Apply (defaultArg y)]) . map unArg
            -- a nested pair as a point, under the binders i j
            unnest :: Term -> Term
            unnest s = rebuild 2
              [ v <$ argFromDom dom | (dom, v) <- zip doms (sigmaProjs pfst psnd (length doms) s) ]
            -- the edge λ k → h (args k) as a path of nested pairs
            nestP :: Abs [Arg Term] -> Term
            nestP args = Lam defaultArgInfo (nest <$> args)
            s00 = nest (absApp argsL iZ)
            s01 = nest (absApp argsL iO)
            s10 = nest (absApp argsR iZ)
            s11 = nest (absApp argsR iO)
            surrogate = apply tmSqFill $
              [ hide $ defaultArg (Level lSigma), defaultArg sigmaT
              , hide $ defaultArg s00, hide $ defaultArg s01, defaultArg (nestP argsL)
              , hide $ defaultArg s10, hide $ defaultArg s11, defaultArg (nestP argsR)
              , defaultArg (nestP argsU), defaultArg (nestP argsD) ]
          reportSDoc "cubical.prim.uip" 40 $ "the surrogate is" <+> prettyTCM surrogate
          fmap Just $ runNamesT [] $ do
            sq   <- open surrogate
            l'   <- open (nestP argsL)
            r'   <- open (nestP argsR)
            u'   <- open (nestP argsU)
            d'   <- open (nestP argsD)
            s00' <- open s00
            s01' <- open s01
            s10' <- open s10
            s11' <- open s11
            lam "i" \i -> lam "j" \j ->
              unnest <$> (sq <@@> (l', r', i)
                             <@@> (u' <@@> (s00', s10', i), d' <@@> (s01', s11', i), j))

-- | Squares of types, i.e. prim^sqFillData at a universe. The universe is treated as an
--   inductive type whose constructors are the type formers, but only here, in the
--   implementation: there is no typecase in the object theory. So, as for data types, the square
--   only reduces when all four edges are headed by the same type former, and is then computed
--   in the nested Σ of the former's arguments by 'fillVia':
--
--   * Π: the arguments are @(A : Type ℓ) (B : A → Type ℓ')@; the hiding and modality of the
--     domain must agree on all edges.
--   * @PathP {ℓ} A x y@: the line A is packed as a path, @(A₀ A₁ : Type ℓ) (A : A₀ ≡ A₁) (x : A₀)
--     (y : A₁)@. This includes the non-dependent paths @x ≡ y@, which unfold to PathP.
--   * Other definitions @q es@ (data types, records, Σ, but also stuck type families): the
--     arguments are q's telescope. A prefix of arguments that cannot be packed into a Σ, like
--     levels, must be constant along the edges.
--
--   If all four edges are constant (e.g. @refl@ at a neutral type), so are the corners and the
--   square is constant.
--
--   [TODO] Levels are required to be constant along the edges (sorts of the domain and codomain
--   of a Π, the level of a PathP, level arguments of definitions). Levels could depend on I, but
--   this is not supported yet: such squares are stuck.
sqFillUniv :: [Term] -- ^ the corners and edges: a₀₀ a₀₁ a₀₋ a₁₀ a₁₁ a₁₋ a₋₀ a₋₁
           -> ReduceM (Maybe Term)
sqFillUniv [x00, x01, el, x10, x11, er, eu, ed] = do
  bodies@[bL, bR, bU, bD] <- mapM edgeBody [(x00, x01, el), (x10, x11, er), (x00, x10, eu), (x01, x11, ed)]
  mPathP <- getBuiltinName' builtinPathP
  mLevel <- getBuiltinName' builtinLevel
  if all (isJust . constAlongEdge . unAbs) bodies
    then Just <$> runNamesT [] (open x00 >>= \x -> lam "i" \_ -> lam "j" \_ -> x)
    else case unAbs bL of

    -- Π
    Pi aL bBL
      | Just parts <- mapM piParts bodies
      , all (sameDom aL . fst) parts
      -> do
        sA <- reduce $ getSort (unDom aL)
        sB <- reduce $ getSort (absBody bBL)
        case (constAlongEdge sA, constAlongEdge =<< constAlongEdge sB) of
          (Just sA', Just sB') -> do
            reportSDoc "cubical.prim.uip" 40 $ "all edges are Π types"
            let doms =
                  [ defaultDom ("A", sort sA')
                  , defaultDom ("B", El (FunSort (raise 1 sA') (univSort (raise 1 sB'))) $
                      Pi (defaultDom (El (raise 1 sA') (var 0))) (NoAbs "_" (sort (raise 1 sB')))) ]
                args (a, b) = [defaultArg (unEl (unDom a)), defaultArg (Lam defaultArgInfo (unEl <$> b))]
                rebuild n = \case
                  [a, b] -> Pi (setDom aL (El (raise n sA') (unArg a))) $
                    Abs (absName bBL) $ El (raise (n + 1) sB') $ raise 1 (unArg b) `apply` [defaultArg (var 0)]
                  _ -> __IMPOSSIBLE__
                [argsL, argsR, argsU, argsD] = zipWith (\b ps -> Abs (absName b) (args ps)) bodies parts
            fillVia doms rebuild argsL argsR argsU argsD
          _ -> pure Nothing

    -- PathP
    Def q [Apply lvL, Apply _, Apply _, Apply _]
      | Just q == mPathP
      , Just parts <- mapM (pathPParts q . unAbs) bodies
      , Just lv <- constAlongEdge (unArg lvL)
      -> do
        reportSDoc "cubical.prim.uip" 40 $ "all edges are PathP types"
        iZ <- getTerm "for SqFillUniv" builtinIZero
        iO <- getTerm "for SqFillUniv" builtinIOne
        let lvl n = case raise n lv of
              Level l -> l
              t       -> atomicLevel t
            pathP l bA x y = Def q $ map Apply
              [ setHiding Hidden $ defaultArg (Level l), defaultArg bA, defaultArg x, defaultArg y ]
            -- in context Γ, A₀ A₁ A x y
            doms =
              [ defaultDom ("A₀", sort (Type (lvl 0)))
              , defaultDom ("A₁", sort (Type (lvl 1)))
              , defaultDom ("A", El (Type (levelSuc (lvl 2))) $
                  pathP (levelSuc (lvl 2)) (Lam defaultArgInfo (NoAbs "_" (Sort (Type (lvl 2))))) (var 1) (var 0))
              , defaultDom ("x", El (Type (lvl 3)) (var 2))
              , defaultDom ("y", El (Type (lvl 4)) (var 2)) ]
            -- the line as a path, under the edge variable k
            args (bA, x, y) =
              [ defaultArg (bA `apply` [defaultArg iZ]), defaultArg (bA `apply` [defaultArg iO])
              , defaultArg (Lam defaultArgInfo (Abs "i" (raise 1 bA `apply` [defaultArg (var 0)])))
              , defaultArg x, defaultArg y ]
            rebuild n = \case
              [a0, a1, bA, x, y] -> pathP (lvl n)
                (Lam defaultArgInfo (Abs "i" (raise 1 (unArg bA) `applyE` [IApply (raise 1 (unArg a0)) (raise 1 (unArg a1)) (var 0)])))
                (unArg x) (unArg y)
              _ -> __IMPOSSIBLE__
            [argsL, argsR, argsU, argsD] = zipWith (\b ps -> Abs (absName b) (args ps)) bodies parts
        fillVia doms rebuild argsL argsR argsU argsD

    -- other definitions
    Def q esL
      | Just argsLs <- properApplies esL
      , Just argss <- mapM (defArgs q . unAbs) bodies
      -> do
        tel <- theTel <$> (telView . defType =<< getConstInfo q)
        -- the prefix of arguments that cannot be packed into a Σ must be constant
        let isLevel t = case unEl t of
              Def l [] -> Just l == mLevel
              _        -> False
            splitConst consts tel'@(ExtendTel d rest) (a : as) = do
              s <- reduce $ getSort (unDom d)
              case s of
                Type{} | not (isLevel (unDom d)) -> pure $ Just (reverse consts, tel')
                _ -> case constAlongEdge a of
                  Just a' -> splitConst (a' : consts) (absApp rest (unArg a')) as
                  Nothing -> pure Nothing
            splitConst consts tel' _ = pure $ Just (reverse consts, tel')
        -- the edges must be fully applied
        (if size tel /= length argsLs then pure Nothing else splitConst [] tel argsLs) >>= \case
          Nothing -> pure Nothing
          Just (consts, tel') -> do
            reportSDoc "cubical.prim.uip" 40 $ "all edges are headed by" <+> prettyTCM q
            let n = length consts
                [argsL, argsR, argsU, argsD] = zipWith (\b as -> Abs (absName b) (drop n as)) bodies argss
                rebuild n fields = Def q $ map Apply (raise n consts ++ fields)
            fillVia (telToList tel') rebuild argsL argsR argsU argsD

    _ -> pure Nothing
  where
    piParts :: Abs Term -> Maybe (Dom Type, Abs Type)
    piParts b = case unAbs b of
      Pi a c -> Just (a, c)
      _      -> Nothing
    sameDom a a' = getHiding a == getHiding a' && getModality a == getModality a'
    -- the domain with the given type, dropping its tactic and rewrite annotations
    setDom (Dom ai nm fin _ _ _) t = Dom ai nm fin Nothing Nothing t
    pathPParts q (Def q' [Apply _, Apply bA, Apply x, Apply y]) | q == q' = Just (unArg bA, unArg x, unArg y)
    pathPParts _ _ = Nothing
    defArgs q (Def q' es) | q == q' = properApplies es
    defArgs _ _ = Nothing
sqFillUniv _ = __IMPOSSIBLE__

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
                -- Empty records with eta are unit types: the constant square has the right
                -- boundary by eta, so no Σ (and no level) is needed.
                Record{recFields = [], recConHead = conR, recEtaEquality' = eta}
                  | YesEta <- theEtaEquality eta -> do
                    ret <- runNamesT [] $ do
                      let hlam = glam (setHiding Hidden defaultArgInfo)
                      hlam "a₀₀" \_ -> hlam "a₀₁" \_ -> lam "a₀₋" \_ ->
                        hlam "a₁₀" \_ -> hlam "a₁₁" \_ -> lam "a₁₋" \_ ->
                        lam "a₋₀" \_ -> lam "a₋₁" \_ -> lam "i" \_ -> lam "j" \_ ->
                        pure $ Con conR ConOSystem []
                    redReturn $ ret `apply` rest

                -- tel = params ++ telFields
                Record{recFields = fields, recTel = tel, recEtaEquality' = eta, recConHead = conR}
                  -- [TODO] think about pattern matching records
                  | not (NoEta PatternMatching == theEtaEquality eta), Just as <- allApplyElims es -> do
                    -- recTel includes the parameters, instantiate them to get the field telescope.
                    let fieldDoms = telToList $ tel `apply` as
                    mSigmaProjs <- sigmaKit
                    case mSigmaProjs of
                      Nothing -> nored lc sbC rest -- the SIGMA builtin is not bound
                      Just (sigma, pair, pfst, psnd) -> do
                        -- [TODO] irrelevant fields cannot be nested into a Σ
                        mSigmaRecord <- if all isRelevant fieldDoms
                          then telListToSigma sigma pfst psnd $ map (snd . unDom) fieldDoms
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
                          _ -> nored lc sbC rest

                -- Data types (not indexed, not higher inductive): computing the square needs its
                -- edges, so hand over to prim^sqFillData, which takes all 10 arguments of the
                -- square except the interval variables. If it is not declared, data types are stuck.
                Datatype{dataIxs = 0, dataHIT = NotHIT} ->
                  getTerm' builtin_sqFillData >>= \case
                    Just tmSqFillData -> redReturn $ tmSqFillData `apply` (lc : bC : rest)
                    Nothing           -> nored lc sbC rest

                r@Record{recEtaEquality' = eta} -> do
                  reportSDoc "cubical.prim.uip" 40 $ pshow eta
                  nored lc sbC rest
                  
                _ -> do
                  reportSDoc "cubical.prim.uip" 40 $ "we are getting unmatched def type" <+> prettyTCM tbC
                  reportSDoc "cubical.prim.uip" 40 $ "the qname is" <+> prettyTCM q
                  nored lc sbC rest

            -- Universes: as for data types, computing the square needs its edges, so hand over to
            -- prim^sqFillData (see sqFillUniv).
            Sort _ ->
              getTerm' builtin_sqFillData >>= \case
                Just tmSqFillData -> redReturn $ tmSqFillData `apply` (lc : bC : rest)
                Nothing           -> nored lc sbC rest

            --
            t -> do
              reportSDoc "cubical.prim.uip" 40 $ "we are getting type" <+> prettyTCM tbC
              reportSDoc "cubical.prim.uip" 60 $ "internal representation:" <+> pretty tbC
              nored lc sbC rest

      where
        -- Must return all arity (= 2) arguments, see reducePrimitive.
        nored lc sbC rest = return $ NoReduction $ [notReduced lc, reduced sbC] ++ map notReduced rest


-- | The data type and universe cases of prim^sqFill, which reduces to this primitive. It takes
--   all 10 arguments of the square except the interval variables, so that it can inspect the
--   edges. (The interval arguments i j are path applications, which reducePrimitive would turn
--   into plain applications if they were part of the arity.)
--
--   For data types, like hcomp on data types (compData in Agda.TypeChecking.Primitive.Cubical),
--   it only reduces when all four edges are headed by the same constructor c. The square is
--   then computed in the nested sigma of c's arguments by 'fillVia', as for records.
--   Recursive arguments recurse through prim^sqFill. For universes, see 'sqFillUniv'.
prim_sqFillData' :: TCM PrimitiveImpl
prim_sqFillData' = do
  requireCubical CUip
  t <- runNamesT [] $
       hPi' "l" (el $ cl primLevel) $ \ la ->
       nPi' "A" (sort . tmSort <$> la) $ \ bA ->
       el $ primSqFill <#> la <@> bA

  return $ PrimImpl t $
    PrimFun __IMPOSSIBLE__ 10 [] $ \ts _nelims -> case ts of
      lc : bC : rest@[ax00, ax01, ael, ax10, ax11, aer, aeu, aed] -> do
        sbC <- reduceB' bC
        let tbC = unArg $ ignoreBlocking sbC
            [x00, x01, el, x10, x11, er, eu, ed] = map unArg [ax00, ax01, ael, ax10, ax11, aer, aeu, aed]
            -- Must return all arity (= 10) arguments, see reducePrimitive.
            nored = return $ NoReduction $ [notReduced lc, reduced sbC] ++ map notReduced rest
            orNored = maybe nored redReturn
        case tbC of
          Def q es -> theDef <$> getConstInfo q >>= \case
            Datatype{dataIxs = 0, dataHIT = NotHIT} | Just pars <- allApplyElims es -> do
              reportSDoc "cubical.prim.uip" 40 $ "we have a data type" <+> prettyTCM tbC
              edges <- mapM edgeCon [(x00, x01, el), (x10, x11, er), (x00, x10, eu), (x01, x11, ed)]
              case edges of
                [Just (c, argsL), Just (cR, argsR), Just (cU, argsU), Just (cD, argsD)]
                  | all ((conName c ==) . conName) [cR, cU, cD] -> do
                  argDoms <- telToList . theTel <$>
                    (telView . (`piApply` pars) . defType =<< getConstInfo (conName c))
                  reportSDoc "cubical.prim.uip" 40 $ "all edges are headed by" <+> prettyTCM (conName c)
                  orNored =<< fillVia argDoms (\_ -> Con c ConOSystem . map Apply) argsL argsR argsU argsD
                _ -> nored
            _ -> nored
          Sort _ -> do
            reportSDoc "cubical.prim.uip" 40 $ "we have a universe" <+> prettyTCM tbC
            orNored =<< sqFillUniv [x00, x01, el, x10, x11, er, eu, ed]
          _ -> nored
      _ -> __IMPOSSIBLE__


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
