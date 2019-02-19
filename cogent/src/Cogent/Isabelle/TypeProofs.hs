--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuasiQuotes #-}

module Cogent.Isabelle.TypeProofs where

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core
import Cogent.Inference
import Cogent.Isabelle.Deep (deepDefinitions, deepTypeAbbrevs, getTypeAbbrevs, TypeAbbrevs)
import Cogent.Isabelle.ProofGen
import Cogent.Util (NameMod)
import Data.LeafTree
import Data.Vec hiding (splitAt, length, zipWith, zip, unzip, head)
import Data.Nat
import qualified Data.Vec as V

import Control.Arrow (second)
import Control.Monad.State.Strict
import Data.Maybe (mapMaybe)
import Data.Char
import Data.Foldable
import Data.List
import qualified Data.Map as M
import Data.Ord (comparing)
import Isabelle.ExprTH
import qualified Isabelle.InnerAST as I
import Isabelle.InnerAST hiding (Type)
import Isabelle.OuterAST as O
import Numeric
#if __GLASGOW_HASKELL__ >= 709
import Prelude hiding ((<$>))
#endif
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen hiding ((</>))
import Text.Printf
import Text.Show
import Lens.Micro ((^.))
import Lens.Micro.Mtl (use)

--
-- This module generates the proofs that Isabelle uses to check the typing of
-- Cogent expressions.
--

type IsaCtx t = [Maybe (Type t)]

-- #Explicit Context Splitting Operations
data TypeSplitKind = TSK_R | TSK_L | TSK_S | TSK_NS
    deriving (Show, Eq)

type TreeCtx t = (IsaCtx t, TypingTree t)

data TypingTree t =
    TyTrLeaf
    | TyTrFun FunName
    | TyTrDup (TreeCtx t) (TreeCtx t)
    | TyTrSplit [Maybe TypeSplitKind] (TreeCtx t) (TreeCtx t)
    deriving (Show, Eq)

deepTypeProof :: (Pretty a) => NameMod -> Bool -> Bool -> String -> [Definition TypedExpr a] -> String -> Doc
deepTypeProof mod withDecls withBodies thy decls log =
    let
        header = (string ("(*\n" ++ log ++ "\n*)\n") <$>)
        ta = getTypeAbbrevs mod decls
        imports = if __cogent_fml_typing_tree
                    then
                        [__cogent_root_dir </> "c-refinement/TypeProofGen",
                        __cogent_root_dir </> "cogent/isa/AssocLookup"]
                    else [__cogent_root_dir </> "cogent/isa/CogentHelper"]
        proofDecls | withDecls = deepTypeAbbrevs mod ta
                                ++ deepDefinitions mod ta decls
                                ++ funTypeEnv mod decls
                                ++ funDefEnv decls
                                ++ concatMap (funTypeTree mod ta) decls
                                ++ cogentFunInfo mod
                    | otherwise = []
        (proofScript, st) = runState (proofs decls) (typingSubproofsInit mod ta)
        subproofs = sortOn (\(proofId, _, _) -> proofId) $
            M.elems (st ^. subproofKinding) ++
            M.elems (st ^. subproofAllKindCorrect) ++
            M.elems (st ^. subproofSplits) ++
            M.elems (st ^. subproofWeakens)
        proofBodies
            | withBodies = -- [TheoryString "ML {* open TTyping_Tactics *}"] ++
                concatMap (\(proofId, prop, script) ->
                            formatSubproof ta (typingSubproofPrefix ++ show proofId) prop script) subproofs ++
                proofScript
            | otherwise = []
    in
        header . pretty $ Theory thy (TheoryImports imports) $ proofDecls ++ proofBodies

splitEvery :: Int -> [a] -> [[a]]
splitEvery = splitEveryW (const 1)

splitEveryW :: (a -> Int) -> Int -> [a] -> [[a]]
splitEveryW _ n [] = []
splitEveryW w n xs = let (as, bs) = span ((<= n) . snd) .
                                    snd . mapAccumL (\s (x, w) -> (s+w, (x, s+w))) 0 $
                                    map (ap (,) w) xs
                     in map fst as : splitEveryW w n (map fst bs)

formatMLProof :: String -> String -> [String] -> [TheoryDecl I.Type I.Term]
formatMLProof name typ lines =
  -- Isabelle has trouble with large numbers of @{thm} antiquotations; split into small blocks
  [ TheoryString $ stepsML $ splitEveryW (length . filter (=='@')) 500 lines ]
  where stepsML (steps:stepss) =
          (if null stepss then "" else stepsML stepss) ++
          "ML_quiet {*\nval " ++ name ++ " : " ++ typ ++ " list = [\n" ++
          intercalate ",\n" steps ++ "\n]" ++
          (if null stepss then "" else " @ " ++ name) ++ " *}\n"
        stepsML [] = "ML_quiet {* val " ++ name ++ " : " ++ typ ++ " list = [] *}\n"

formatSubproof :: TypeAbbrevs -> String -> (Bool, I.Term) -> [Tactic] -> [TheoryDecl I.Type I.Term]
formatSubproof ta name (schematic, prop) steps =
  [ LemmaDecl
    (Lemma schematic
        (Just $ TheoremDecl (Just name) [Attribute "unfolded" ["abbreviated_type_defs"]])
        [prop]
        (Proof ([ Method "simp" ["add: kinding_def abbreviated_type_defs"]]) ProofDone)) ]

formatMLTreeGen :: String -> [TheoryDecl I.Type I.Term]
formatMLTreeGen name =
  [ TheoryString ( "ML_quiet {*\nval " ++ name ++ "_ttyping_details_future"
    ++ " = get_all_typing_details_future @{context} Cogent_info \""
    ++ name
    ++ "\" []\n*}\n"
  ) ]

formatMLTreeFinalise :: String -> [TheoryDecl I.Type I.Term]
formatMLTreeFinalise name =
  [ TheoryString ( "ML_quiet {*\nval (_, "
    ++ name ++ "_typing_tree, " ++ name ++ "_typing_bucket)\n"
    ++ "= Future.join " ++ name ++ "_ttyping_details_future\n*}\n"
  ) ]

formatTypecorrectProof :: String -> [TheoryDecl I.Type I.Term]
formatTypecorrectProof fn =
  [ LemmaDecl (Lemma False (Just $ TheoremDecl (Just (fn ++ "_typecorrect")) [])
          [mkId $ "\\<Xi>, fst " ++ fn ++ "_type, (" ++ fn ++ "_typetree, [Some (fst (snd " ++ fn ++ "_type))]) T\\<turnstile> " ++
                  fn ++ " : snd (snd " ++ fn ++ "_type)"]
    (Proof (if __cogent_fml_typing_tree then [Method "tactic" ["{* resolve_future_typecorrect @{context} " ++ fn ++ "_ttyping_details_future *}"]]
      else [Method "simp" ["add: " ++ fn ++ "_type_def " ++ fn ++ "_def " ++
                           fn ++ "_typetree_def replicate_unfold"
                           ++ " abbreviated_type_defs"],
            Method "tactic" ["{* apply_ttsplit_tacs_simple \"" ++ fn ++ "\"\n"
                    ++ "    @{context} " ++ fn ++ "_typecorrect_script *}"]])
     ProofDone)) ]

-- data TreeSteps a = StepDown | StepUp | Val a
--     deriving (Eq, Read, Show)

-- flattenHintTree :: LeafTree Hints -> [TreeSteps Hints]
-- flattenHintTree (Branch ths) = StepDown : concatMap flattenHintTree ths ++ [StepUp]
-- flattenHintTree (Leaf h) = [Val h]

prove :: (Pretty a) => [Definition TypedExpr a] -> Definition TypedExpr a
      -> State TypingSubproofs ([TheoryDecl I.Type I.Term], [TheoryDecl I.Type I.Term])
prove decls (FunDef _ fn k ti to e) = do
  mod <- use nameMod
  let eexpr = pushDown (Cons (Just ti) Nil) (splitEnv (Cons (Just ti) Nil) e)
--   proofSteps' <- proofSteps decls (fmap snd k) ti eexpr
  ta <- use tsTypeAbbrevs
  let typecorrect_script = formatMLProof (mod fn ++ "_typecorrect_script") "hints treestep" [] -- (map show $ flattenHintTree proofSteps')
  let fn_typecorrect_proof = (if __cogent_fml_typing_tree then formatMLTreeGen (mod fn) else []) ++ formatTypecorrectProof (mod fn)
  return (fn_typecorrect_proof, if __cogent_fml_typing_tree then formatMLTreeFinalise (mod fn) else [])
prove _ _ = return ([], [])

proofs :: (Pretty a) => [Definition TypedExpr a]
       -> State TypingSubproofs [TheoryDecl I.Type I.Term]
proofs decls = do
    bodies <- mapM (prove decls) decls
    return $ concat $ map fst bodies ++ map snd bodies

funTypeTree :: (Pretty a) => NameMod -> TypeAbbrevs -> Definition TypedExpr a -> [TheoryDecl I.Type I.Term]
funTypeTree mod ta (FunDef _ fn _ ti _ e) = [deepTyTreeDef mod ta fn (typeTree eexpr)]
  where eexpr = pushDown (Cons (Just ti) Nil) (splitEnv (Cons (Just ti) Nil) e)
funTypeTree _ _ _ = []

deepTyTreeDef :: NameMod -> TypeAbbrevs -> FunName -> TypingTree t -> TheoryDecl I.Type I.Term
deepTyTreeDef mod ta fn e = let ttfn = mkId $ mod fn ++ "_typetree"
                                tt = deepCtxTree mod ta e
                             in [isaDecl| definition "$ttfn \<equiv> $tt" |]

deepTypeSplitKind :: TypeSplitKind -> Term
deepTypeSplitKind TSK_R  = mkId "TSK_R"
deepTypeSplitKind TSK_L  = mkId "TSK_L"
deepTypeSplitKind TSK_S  = mkId "TSK_S"
deepTypeSplitKind TSK_NS = mkId "TSK_NS"

deepTreeSplits :: [Maybe TypeSplitKind] -> Term
deepTreeSplits (Nothing : Nothing : tsks) = mkApp (mkId "append") [repl, rest]
  where
    n = length (takeWhile (== Nothing) tsks)
    rest = deepTreeSplits (drop n tsks)
    repl = mkApp (mkId "replicate") [mkInt (toInteger n + 2), deepMaybe Nothing]
deepTreeSplits (tsk : tsks) = mkApp (mkId "Cons")
    [deepMaybe (fmap deepTypeSplitKind tsk), deepTreeSplits tsks]
deepTreeSplits [] = mkList []

deepCtx :: NameMod -> TypeAbbrevs -> [Maybe (Type t)] -> Term
deepCtx mod ta = mkList . map (deepMaybeTy mod ta)

deepCtxTree :: NameMod -> TypeAbbrevs -> TypingTree t -> Term
deepCtxTree _ _ TyTrLeaf = mkId "TyTrLeaf"
deepCtxTree mod ta (TyTrFun fnName) =
    mkApp (mkId "TyTrFun") [mkString fnName]
deepCtxTree mod ta (TyTrDup (lctx, l) (rctx, r)) =
    mkApp (mkId "TyTrDup") [deepCtx mod ta lctx, deepCtxTree mod ta l, deepCtx mod ta rctx, deepCtxTree mod ta r]
deepCtxTree mod ta (TyTrSplit f (lctx, l) (rctx, r)) =
  mkApp (mkId "TyTrSplit") [deepTreeSplits f, deepCtx mod ta lctx, deepCtxTree mod ta l, deepCtx mod ta rctx, deepCtxTree mod ta r]

-- dodgy fix
escapedFunName :: FunName -> String
escapedFunName fn | '\'' `elem` fn = "[" ++ intercalate "," (repr fn) ++ "]"
                  | otherwise = "''" ++ fn ++ "''"
                  where
                    repr :: String -> [String]
                    repr x = if all isAscii x
                                    then map (printf "CHR %#02x" . ord) x
                                    else error "Function name contained a non-ascii char! Isabelle doesn't support this."

funTypeCase :: NameMod -> Definition TypedExpr a -> Maybe (String, String)
funTypeCase mod (FunDef  _ fn _ _ _ _) = Just (fn, mod fn ++ "_type")
funTypeCase mod (AbsDecl _ fn _ _ _  ) = Just (fn, mod fn ++ "_type")
funTypeCase _ _ = Nothing

funTypeEnv :: NameMod -> [Definition TypedExpr a] -> [TheoryDecl I.Type I.Term]
funTypeEnv mod fs =
    let upds = map (\(a,b) -> (mkId $ escapedFunName a, mkId b))
                $ sortBy (\p q -> compare (fst p) (fst q)) $ mapMaybe (funTypeCase mod) fs
    in funTypeEnv' $ mkList $ map (uncurry mkPair) upds

funTypeEnv' upds = let -- NOTE: as the isa-parser's antiQ doesn't handle terms well and it doesn't
                       -- keep parens, we have to fall back on strings / zilinc
                       tysig = [isaType| string \<Rightarrow> (Cogent.kind list \<times> Cogent.type \<times> Cogent.type) option |]
                    in [[isaDecl| definition \<Xi> :: "$tysig"
                                  where "\<Xi> \<equiv> assoc_lookup ($upds)" |]]

funDefCase :: Definition TypedExpr a -> Maybe (Term, Term)
funDefCase (AbsDecl _ fn _ _ _  ) = Just (mkId $ escapedFunName fn, mkId "(\\<lambda>_ _. False)")
funDefCase _ = Nothing

funDefEnv :: [Definition TypedExpr a] -> [TheoryDecl I.Type I.Term]
funDefEnv fs = funDefEnv' $ mkList $ map (uncurry mkPair) $ mapMaybe funDefCase fs

funDefEnv' upds = [[isaDecl| definition "\<xi> \<equiv> assoc_lookup ($upds)" |]]

-- TODO a little hacky, redoing work we've done earlier / v.jackson
-- FIXME we're assuming mod will just do a prefix!!!!  / v.jackson
cogentFunInfo :: NameMod -> [TheoryDecl I.Type I.Term]
cogentFunInfo mod =
    [TheoryString $
        "ML {*\n" ++
        "val Cogent_info = {\n" ++
        "  xidef = @{thms \\<Xi>_def \\<xi>_def},\n" ++
        "  absfuns = map (prefix \"" ++ pfxStr  ++
            "\" #> suffix \"_type_def\") Cogent_abstract_functions\n" ++
        "          |> maps (Proof_Context.get_thms @{context}),\n" ++
        "  funs = map (prefix \"" ++ pfxStr ++
            "\" #> suffix \"_type_def\") Cogent_functions\n" ++
        "          |>  maps (Proof_Context.get_thms @{context}),\n" ++
        "  type_defs = @{thms abbreviated_type_defs}" ++
        "}\n" ++
        "*}"]
    where
        pfxStr = mod ""

(<\>) :: Vec v (Maybe t) -> Vec v (Maybe t) -> Vec v (Maybe t)
(<\>) (Cons x xs) (Cons Nothing ys)  = Cons x       $ xs <\> ys
(<\>) (Cons _ xs) (Cons (Just _) ys) = Cons Nothing $ xs <\> ys
(<\>) Nil Nil = Nil
#if __GLASGOW_HASKELL__ < 711
(<\>) _ _ = error "TypeProofs: unreachable case in <\\>: vectors have mismatching lengths"
#endif

setAt :: [a] -> Int -> a -> [a]
setAt (x:xs) 0 v = v:xs
setAt (x:xs) n v = x:setAt xs (n-1) v
setAt [] _ _ = []

recTaken = snd . snd
recType = fst . snd

bangEnv :: [(Fin v, a)] -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t))
bangEnv ((t, _):is) env = bangEnv is $ update env t $ fmap bang $ env `at` t
bangEnv [] env = env

unbangEnv :: Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t))
unbangEnv Nil Nil = Nil
unbangEnv (Cons (Just _) bs) (Cons e es) = Cons e (unbangEnv bs es)
unbangEnv (Cons Nothing bs)  (Cons _ es) = Cons Nothing (unbangEnv bs es)

selectEnv :: [(Fin v, a)] -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t))
selectEnv [] env = cleared env
selectEnv ((v,_):vs) env = update (selectEnv vs env) v (env `at` v)

-- Annotates a typed expression with the environment required to successfully execute it
splitEnv :: (Pretty a) => Vec v (Maybe (Type t)) -> TypedExpr t v a -> EnvExpr t v a
splitEnv env (TE t Unit)          = EE t Unit          $ cleared env
splitEnv env (TE t (ILit i t'))   = EE t (ILit i t')   $ cleared env
splitEnv env (TE t (SLit s))      = EE t (SLit s)      $ cleared env
splitEnv env (TE t (Fun f ts nt)) = EE t (Fun f ts nt) $ cleared env
splitEnv env (TE t (Variable v))  = EE t (Variable v)  $ singleton (fst v) env

splitEnv env (TE t (Esac e))
    = let e' = splitEnv env e
       in EE t (Esac e') $ envOf e'

splitEnv env (TE t (Promote ty e))
    = let e' = splitEnv env e
       in EE t (Promote ty e') $ envOf e'

splitEnv env (TE t (Cast ty e))
    = let e' = splitEnv env e
       in EE t (Cast ty e') $ envOf e'

splitEnv env (TE t (Member e f))
    = let e' = splitEnv env e
       in EE t (Member e' f) $ envOf e'

splitEnv env (TE t (Struct fs))
    = let fs' = map (splitEnv env . snd) fs
       in EE t (Struct (zip (map fst fs) fs')) $ foldl (<|>) (cleared env) (map envOf fs')

splitEnv env (TE t (Op o es))
    = let vs = map (splitEnv env) es
       in EE t (Op o vs) $ foldl (<|>) (cleared env) (map envOf vs)

splitEnv env (TE t (App e1 e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv env e2
       in EE t (App e1' e2') $ envOf e1' <|> envOf e2'

splitEnv env (TE t (Tuple e1 e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv env e2
       in EE t (Tuple e1' e2') $ envOf e1' <|> envOf e2'

splitEnv env (TE t (Put e1 f e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv env e2
       in EE t (Put e1' f e2') $ envOf e1' <|> envOf e2'

splitEnv env (TE t (Split a e1 e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv (Cons (Just t1) $ Cons (Just t1') env) e2
          TProduct t1 t1' = typeOf e1'
       in EE t (Split a e1' e2') $ envOf e1' <|> peel2 (envOf e2')

splitEnv env (TE t (Let a e1 e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv (Cons (Just $ typeOf e1') env) e2
       in EE t (Let a e1' e2') $ envOf e1' <|> peel (envOf e2')

splitEnv env (TE t (LetBang vs a e1 e2))
    = let env' = bangEnv vs env
          e1' = splitEnv env' e1
          -- type system requires pushing down vs, even if unused in e1
          e1'' = pushDown (selectEnv vs env' <\> envOf e1') e1'
          e2' = splitEnv (Cons (Just $ typeOf e1'') env) e2
       in EE t (LetBang vs a e1'' e2') $ unbangEnv (envOf e1'') env' <|> peel (envOf e2')

splitEnv env (TE t (Con tag e tau)) =
    let e' = splitEnv env e
     in EE t (Con tag e' tau) $ envOf e'

splitEnv env (TE t (If ec et ee))
    = let ec' = splitEnv env ec
          et' = splitEnv env et
          ee' = splitEnv env ee
       in EE t (If ec' et' ee') $ envOf ec' <|> envOf et' <|> envOf ee'

splitEnv env (TE t (Case e tag (lt,at,et) (le,ae,ee)))
    = let et' = splitEnv (Cons (fmap fst $ lookup tag ts) env) et
          restt = TSum $ adjust tag (second $ const True) ts
          ee' = splitEnv (Cons (Just restt) env) ee
          e'  = splitEnv env e
          TSum ts = typeOf e'
       in EE t (Case e' tag (lt,at,et') (le,ae,ee')) $ envOf e' <|> peel (envOf ee') <|> peel (envOf et')

splitEnv env (TE t (Take a e f e2)) =
    let e' = splitEnv env e
        TRecord ts s = typeOf e'
        e2' = splitEnv (Cons (Just $ recType (ts!!f)) (Cons (Just $ TRecord (setAt ts f (fst (ts!!f), (recType (ts!!f), True))) s) env)) e2
     in EE t (Take a e' f e2') $ envOf e' <|> peel2 (envOf e2')


-- Ensures that the environment of an expression is equal to the sum of the
-- environments of the subexpressions.
pushDown :: (Pretty a) => Vec v (Maybe (Type t)) -> EnvExpr t v a -> EnvExpr t v a
pushDown unused (EE ty e@Unit      _) = EE ty e unused
pushDown unused (EE ty e@(ILit {}) _) = EE ty e unused
pushDown unused (EE ty e@(SLit {}) _) = EE ty e unused
pushDown unused (EE ty e@(Fun  {}) _) = EE ty e unused
pushDown unused (EE ty e@(Variable _) env) = EE ty e $ unused <|> env

-- This case may be impossible to prove if unused is non-empty (!!)
pushDown unused (EE ty (Op o []) env) = error "TypeProofs: empty Op" -- EE ty (Op o []) $ unused <|> env

pushDown unused (EE ty (Op o (t:ts)) env)
    = let es = pushDown (unused <\> env) t:map (pushDown (cleared env)) ts
       in EE ty (Op o es) $ unused <|> env

pushDown unused (EE ty (Struct fs) env)
    = let fs' = case map snd fs of
                  (t:ts) -> pushDown (unused <\> env) t:map (pushDown (cleared env)) ts
                  []     -> error "TypeProofs: empty Struct" -- [] -- This case may be impossible to prove if unused is non-empty (!!)
       in EE ty (Struct $ zip (map fst fs) fs') $ unused <|> env

pushDown unused (EE ty (App e1 e2) env)
    = let e1' = pushDown (unused <\> env) e1
          e2' = pushDown (cleared env)    e2
       in EE ty (App e1' e2') $ unused <|> env

pushDown unused (EE ty (Let a e1 e2) env)
    = let e1'@(EE t _ _) = pushDown (unused <\> env) e1
          e2' = pushDown (Cons (Just t) (cleared env)) e2
       in EE ty (Let a e1' e2') $ unused <|> env

pushDown unused (EE ty (LetBang vs a e1 e2) env)
    = let -- e1 already pushed down in splitEnv
          e2vs = selectEnv vs env <\> peel (envOf e2)
          e2' = pushDown (Cons (Just (eexprType e1)) (e2vs <|> ((unused <\> env) <\> envOf e1))) e2
       in EE ty (LetBang vs a e1 e2') $ unused <|> env

pushDown unused (EE ty (Tuple e1 e2) env)
    = let e1' = pushDown (unused <\> env) e1
          e2' = pushDown (cleared env) e2
       in EE ty (Tuple e1' e2') $ unused <|> env

pushDown unused (EE ty (Con tag e t) env)
    = let e' = pushDown unused e
       in EE ty (Con tag e' t) $ unused <|> env

pushDown unused (EE ty (If ec et ee) env)
    = let ec' = pushDown (unused <\> env) ec
          et' = pushDown (envOf ee <\> envOf et) et
          ee' = pushDown (envOf et <\> envOf ee) ee
       in EE ty (If ec' et' ee') $ unused <|> env

pushDown unused (EE ty (Case e tag (lt,at,et) (le,ae,ee)) env)
    = let e'@(EE (TSum ts) _ _) = pushDown (unused <\> env) e
          et' = pushDown (Cons (fmap fst $ lookup tag ts) (peel (envOf ee) <\> peel (envOf et))) et
          restt = TSum $ adjust tag (second $ const True) ts
          ee' = pushDown (Cons (Just restt) (peel (envOf et) <\> peel (envOf ee))) ee
      in (EE ty (Case e' tag (lt,at,et') (le,ae,ee')) $ unused <|> env)

pushDown unused (EE ty (Esac e) env)
    = let e' = pushDown unused e
       in EE ty (Esac e') $ unused <|> env

pushDown unused (EE ty (Split a e1 e2) env)
    = let e1'@(EE (TProduct x y) _ _) = pushDown (unused <\> env) e1
          e2' = pushDown (Cons (Just x) (Cons (Just y) (cleared env))) e2
       in EE ty (Split a e1' e2') $ unused <|> env

pushDown unused (EE ty (Member e f) env)
    = let e' = pushDown unused e
       in EE ty (Member e' f) $ unused <|> env

pushDown unused (EE ty (Take a e f e2) env)
    = let e'@(EE rt _ _) = pushDown (unused <\> env) e
          TRecord ts s = rt
          e2' = pushDown (Cons (Just $ recType $ ts!!f) (Cons (Just $ TRecord (setAt ts f (fst (ts!!f), (recType $ ts!!f, True))) s) (cleared env))) e2
       in EE ty (Take a e' f e2') $ unused <|> env

pushDown unused (EE ty (Put e1 f e2) env)
    = let e1' = pushDown (unused <\> env) e1
          e2' = pushDown (cleared env) e2
       in EE ty (Put e1' f e2') $ unused <|> env

pushDown unused (EE ty (Promote ty' e) env)
    = let e' = pushDown unused e
       in EE ty (Promote ty' e') $ unused <|> env

pushDown unused (EE ty (Cast ty' e) env)
    = let e' = pushDown unused e
       in EE ty (Cast ty' e') $ unused <|> env

pushDown _ e = __impossible $ "pushDown:" ++ show (pretty e) ++ " is not yet implemented"

treeSplit :: Maybe (Type t) -> Maybe (Type t) -> Maybe (Type t) -> Maybe TypeSplitKind
treeSplit Nothing  Nothing  Nothing  = Nothing
treeSplit (Just t) (Just _) Nothing  = Just TSK_L
treeSplit (Just t) Nothing  (Just _) = Just TSK_R
treeSplit (Just t) (Just _) (Just _) = Just TSK_S
treeSplit (Just t) Nothing  Nothing  =
    error $ "bad split: tried to drop '" ++ show t ++ "'"
treeSplit g x y = error $ "bad split: " ++ show (g, x, y)

treeSplits :: Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> [Maybe TypeSplitKind]
treeSplits (Cons g gs) (Cons x xs) (Cons y ys) = treeSplit g x y : treeSplits gs xs ys
treeSplits Nil         Nil         Nil         = []
#if __GLASGOW_HASKELL__ < 711
treeSplits _ _ _ = __ghc_t4139 "TypeProofs.treeSplits"
#endif

treeBang :: Int -> [Int] -> [Maybe TypeSplitKind] -> [Maybe TypeSplitKind]
treeBang i is (x:xs) | i `elem` is = Just TSK_NS:treeBang (i+1) is xs
                     | otherwise   = x:treeBang (i+1) is xs
treeBang i is [] = []

mergeCtx :: Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t))
mergeCtx (Cons Nothing as)  (Cons Nothing bs)  = Cons Nothing (mergeCtx as bs)
mergeCtx (Cons Nothing as)  (Cons (Just b) bs) = Cons (Just b) (mergeCtx as bs)
mergeCtx (Cons (Just a) as) (Cons Nothing bs)  = Cons (Just a) (mergeCtx as bs)
mergeCtx (Cons (Just a) as) (Cons (Just b) bs) =
    if a == b
        then Cons (Just a) (mergeCtx as bs)
        else error $ "Tried to merge two unequal types! " ++ show a ++ ", " ++ show b
mergeCtx Nil Nil = Nil

typeTree :: EnvExpr t v a -> TypingTree t
typeTreeAll :: SNat v -> [EnvExpr t v a] -> (Vec v (Maybe (Type t)), TypingTree t)

typeTree (EE ty (Variable (i, a)) env) = TyTrLeaf
typeTree (EE ty (Fun name ts note) env) = TyTrFun name
typeTree (EE ty (Op op es) env) =
    let (env', tree) = typeTreeAll (V.length env) es
    in if env == env' then tree else error "typeTreeAll generated context incorrect"
typeTree (EE ty (App ea eb) env) =
    TyTrSplit
        (treeSplits env (envOf ea) (envOf eb))
        ([], typeTree ea)
        ([], typeTree eb)
typeTree (EE ty (Con tag e t) env) = typeTree e
typeTree (EE ty Unit env) = TyTrLeaf
typeTree (EE ty (ILit n p) env) = TyTrLeaf
typeTree (EE ty (SLit s) env) = TyTrLeaf
typeTree (EE ty (Let a e1 e2) env) =
    TyTrSplit
        (treeSplits env (envOf e1) (peel $ envOf e2))
        ([], typeTree e1)
        ([envOf e2 `at` FZero], typeTree e2)
typeTree (EE ty (LetBang vs a e1 e2) env) =
    TyTrSplit
        (treeBang 0 (map (finInt . fst) vs) $ treeSplits env (envOf e1) (peel $ envOf e2))
        ([], typeTree e1)
        ([envOf e2 `at` FZero], typeTree e2)
typeTree (EE ty (Tuple ea eb) env) =
    TyTrSplit
        (treeSplits env (envOf ea) (envOf eb))
        ([], typeTree ea)
        ([], typeTree eb)
typeTree (EE ty (Struct fs) env) =
    let (env', tree) = typeTreeAll (V.length env) (map snd fs)
    in if env == env' then tree else error "typeTreeAll generated context incorrect"
typeTree (EE ty (If ec et ee) env) =
    TyTrSplit
        (treeSplits env (envOf ec) (envOf et <|> envOf ee))
        ([], typeTree ec)
        ([], TyTrDup
            -- (treeSplits (envOf ee <|> envOf et) (envOf et) (envOf ee))
            ([], typeTree et)
            ([], typeTree ee))
typeTree (EE ty (Case e tag (lt,at,et) (le,ae,ee)) env) =
    TyTrSplit
        (treeSplits env (envOf e) (peel $ envOf et <|> envOf ee))
        ([], typeTree e)
        ([], TyTrDup
            -- (treeSplits (peel $ envOf ee <|> envOf et) (peel $ envOf et) (peel $ envOf ee))
            ([V.head $ envOf et], typeTree et)
            ([V.head $ envOf ee], typeTree ee))
typeTree (EE ty (Esac e) env) = typeTree e
typeTree (EE ty (Split a e1 e2) env) =
    TyTrSplit
        (treeSplits env (envOf e1) (peel2 $ envOf e2))
        ([], typeTree e1)
        ([envOf e2 `at` FZero, envOf e2 `at` FSuc FZero], typeTree e2)
typeTree (EE ty (Member e i) env) = typeTree e
typeTree (EE ty (Take a e1 f e2) env) =
    TyTrSplit
        (treeSplits env (envOf e1) (peel2 $ envOf e2))
        ([], typeTree e1)
        ([envOf e2 `at` FZero, envOf e2 `at` FSuc FZero], typeTree e2)
typeTree (EE ty (Put ea i eb) env) =
    TyTrSplit
        (treeSplits env (envOf ea) (envOf eb))
        ([], typeTree ea)
        ([], typeTree eb)
typeTree (EE ty (Promote t e) env) = typeTree e
typeTree (EE ty (Cast t e) env) = TyTrLeaf

typeTreeAll n (e : es) =
    let
        (accCtx, accTree) = typeTreeAll n es
        currTree = typeTree e
        currCtx = envOf e
        mergedCtx = mergeCtx currCtx accCtx
    in
        ( mergedCtx
        , TyTrSplit
            (treeSplits mergedCtx currCtx accCtx)
            ([], currTree)
            ([], accTree)
        )
typeTreeAll n [] = (V.repeat n Nothing, TyTrLeaf)