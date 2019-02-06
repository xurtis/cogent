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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Cogent.Isabelle.ProofGen where

import Cogent.Common.Repr
import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core hiding (kind)
import Cogent.Isabelle.Deep
import Cogent.PrettyPrint
import Cogent.Util
-- import Data.LeafTree
import Data.Nat (Nat(Zero, Suc), SNat(SZero, SSuc))
import qualified Data.Nat as Nat
import Data.Vec hiding (splitAt, length, zipWith, zip, unzip)
import qualified Data.Vec as Vec

import Lens.Micro.TH (makeLenses)
import Lens.Micro.Mtl ((%=), (.=), use)
import Control.Monad.State.Strict
import Data.List
import Data.Map (Map)
import Data.Maybe (catMaybes)
import qualified Data.Map as M
import Isabelle.InnerAST hiding (Type)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

type Xi a = [Definition TypedExpr a]
data EnvExpr t v a = EE { eexprType :: Type t
                        , eexprExpr :: Expr t v a EnvExpr
                        , eexprEnv :: Vec v (Maybe (Type t))
                        } deriving (Show)

instance Functor (EnvExpr t v) where
  fmap f (EE t e env) = EE t (ffmap f e) env

instance Prec (EnvExpr t v a) where
  prec (EE _ e _) = prec e

instance (Pretty a) => Pretty (EnvExpr t v a) where
  pretty (EE t e env) = pretty e

data Thm = Thm String
         | NthThm String Int
         | ThmInst String [(String, String)]

data Tactic = RuleTac Thm
            | Simplifier [Thm] [Thm]
            | Force [Thm]
            | WeakeningTac [Thm]
            | SplitsTac Int [(Int, [Tactic])]

instance Show Thm where
  show (Thm thm) = "@{thm " ++ thm ++ "}"
  show (NthThm thm n) = "(nth @{thms " ++ thm ++ "} (" ++ show n ++ "-1))"
  show (ThmInst thm insts) = "@{thm " ++ thm ++ "[where " ++
                                intercalate " and " [ var ++ " = \"" ++ term ++ "\"" | (var, term) <- insts ] ++ "]}"

instance Show Tactic where
  show (RuleTac thm) = "(RTac " ++ show thm ++ ")"
  show (Simplifier adds dels) = "(SimpTac " ++ show (adds, dels) ++ ")"
  show (Force adds) = "(ForceTac " ++ show adds ++ ")"
  show (WeakeningTac kindThms) = "(WeakeningTac " ++ show kindThms ++")"
  show (SplitsTac n tacs) = "(SplitsTac " ++ show (n, tacs) ++ ")"

rule thm = RuleTac (Thm thm)
rule_tac thm insts = RuleTac (ThmInst thm insts)

simp                 = simp_add_del [] []
simp_add thms        = simp_add_del thms []
simp_del thms        = simp_add_del [] thms
simp_add_del add del = Simplifier (map Thm add) (map Thm del)
force_simp add       = Force (map Thm add)

data Hints = KindingTacs [Tactic]
           | TTSplitBangTacs [Tactic]
           | TypingTacs [Tactic]
  deriving Show

-- Same as `Type' in Core, but without type indices.
data Type'
  = TVar' Int
  | TVarBang' Int
  | TCon' TypeName [Type'] (Sigil Representation)
  | TFun' Type' Type'
  | TPrim' PrimInt
  | TString'
  | TSum' [(TagName, (Type', Bool))]
  | TProduct' Type' Type'
  | TRecord' [(FieldName, (Type', Bool))] (Sigil Representation)
  | TUnit'
  deriving (Eq, Ord)

deepType' :: Type' -> Term
deepType' (TVar' v) = mkApp (mkId "TVar") [mkInt $ toInteger v]
deepType' (TVarBang' v) = mkApp (mkId "TVarBang") [mkInt $ toInteger v]
deepType' (TCon' tn ts s) = mkApp (mkId "TCon") [mkString tn, mkList (map deepType' ts), deepSigil s]
deepType' (TFun' ti to) = mkApp (mkId "TFun") [deepType' ti, deepType' to]
deepType' (TPrim' pt) = mkApp (mkId "TPrim") [deepPrimType pt]
deepType' (TString') = mkApp (mkId "TPrim") [mkId "String"]
deepType' (TSum' alts) = mkApp (mkId "TSum") [mkList $ map (\(n,(t,b)) -> mkPair (mkString n) (mkPair (deepType' t) (mkBool b))) alts]
deepType' (TProduct' t1 t2) = mkApp (mkId "TProduct") [deepType' t1, deepType' t2]
deepType' (TRecord' fs s) = mkApp (mkId "TRecord") [mkList $ map (\(fn,(t,b)) -> mkPair (deepType' t) (mkBool b)) fs, deepSigil s]
deepType' (TUnit') = mkId "TUnit"

stripType :: Type t -> Type'
stripType (TVar n) = TVar' (finInt n)
stripType (TVarBang n) = TVarBang' (finInt n)
stripType (TCon t ts s) = TCon' t (map stripType ts) s
stripType (TFun t u) = TFun' (stripType t) (stripType u)
stripType (TPrim t) = TPrim' t
stripType TString = TString'
stripType (TSum ts) = TSum' (map (\(n,(t,b)) -> (n, (stripType t, b))) ts)
stripType (TProduct t u) = TProduct' (stripType t) (stripType u)
stripType (TRecord fs s) = TRecord' (map (\(n,(t,b)) -> (n, (stripType t, b))) fs) s
stripType TUnit = TUnit'

{-
We cache some subproofs to avoid duplication.
This needs to be balanced against the cost of writing out the proof props.
-}
cacheWeakeningProofs = False

typingSubproofPrefix = "typing_helper_" -- prefix for subproof lemma names
type SubproofId = Int
type ProofCache params = Map params (SubproofId,
                                     (Bool, Term), -- (schematic?, prop)
                                     [Tactic])     -- proof
data TypingSubproofs = TypingSubproofs
                       { _genId :: SubproofId
                       , _subproofKinding        :: ProofCache ([Kind], Type', Kind)
                       , _subproofAllKindCorrect :: ProofCache ([Kind], [Type'], [Kind])
                       , _subproofSplits         :: ProofCache (String, [Kind], [Maybe Type'], [Maybe Type'], [Maybe Type'])
                       , _subproofWeakens        :: ProofCache ([Kind], [Maybe Type'], [Maybe Type'])
                       , _tsTypeAbbrevs          :: TypeAbbrevs -- actually just a Reader
                       , _nameMod                :: NameMod
                       }
makeLenses ''TypingSubproofs

thmTypeAbbrev :: String -> State TypingSubproofs Thm
-- we use the "unfolded" theorem attribute when defining thm, instead
{-
thmTypeAbbrev thm = do
  ta <- use tsTypeAbbrevs
  return $ Thm (thm ++ if M.null (fst ta) then "" else "[unfolded " ++ typeAbbrevBucketName ++ "]")
-}
thmTypeAbbrev thm = return (Thm thm)

typingSubproofsInit :: NameMod -> TypeAbbrevs -> TypingSubproofs
typingSubproofsInit mod ta = TypingSubproofs 0 M.empty M.empty M.empty M.empty ta mod

-- newSubproofId = do
--   i <- use genId
--   let i' = i + 1
--   i' `seq` genId .= i'
--   return i'

tacSequence :: [State a [t]] -> State a [t]
tacSequence = fmap concat . sequence


data HintTree a b = Branch a [HintTree a b] | Leaf b

hintListSequence :: Hints -> [State TypingSubproofs (HintTree Hints Hints)] -> State TypingSubproofs (HintTree Hints Hints)
hintListSequence a sths = Branch a <$> sequence sths

-- proofSteps :: Xi a -> Vec t Kind -> Type t -> EnvExpr t v a
--            -> State TypingSubproofs (LeafTree Hints)
-- proofSteps xi k ti x = hintListSequence [ kindingHint k ti, ttyping xi k x ]

ttyping :: Xi a -> Vec t Kind -> EnvExpr t v a -> State TypingSubproofs (HintTree Tactic Tactic)
ttypingAll :: Xi a -> Vec t Kind -> Vec v (Maybe (Type t)) -> [EnvExpr t v a] -> State TypingSubproofs (HintTree Tactic Tactic)

ttyping xi k (EE t (Variable i) env) =
  Branch (rule "ttyping_var") <$>  -- Ξ, K, (TyTrLeaf, Γ) T⊢ Var i : t
    sequence [
      weakens k env (singleton (fst i) env),  -- K ⊢ Γ ↝w singleton (length Γ) i t
      return $ Leaf simp                      -- i < length Γ
    ]

ttyping xi k (EE t' (Fun f ts _) env) =
  case findfun f xi of
    AbsDecl _ _ ks' t u ->
      let ks = fmap snd ks' in
        Branch (rule "ttyping_afun") <$>  -- Ξ, K, (TyTrFun n, Γ) T⊢ AFun f ts : TFun t' u'
          sequence [
            return $ Leaf simp,             -- t' = instantiate ts t
            return $ Leaf simp,             -- u' = instantiate ts u
            do
              ta <- use tsTypeAbbrevs
              mod <- use nameMod
              let unabbrev | M.null (fst ta) = ""
                            | otherwise = "[unfolded " ++ typeAbbrevBucketName ++ "]"
              return $ Leaf $ simp_add ["\\<Xi>_def", mod (coreFunNameToIsabelleName f) ++ "_type_def" ++ unabbrev],
                                        -- Ξ f = Some (K', t, u)

            allKindCorrect k ts ks,     -- list_all2 (kinding K) ts K'
            return $ Leaf simp,         -- instantiate ts (TFun t u)
            wellformed ks (TFun t u),   -- K' ⊢ TFun t u wellformed
            consumed k env              -- K ⊢ Γ consumed
          ]

    FunDef _ _ ks' t u _ ->
      let ks = fmap snd ks' in
        Branch (rule "ttyping_fun") <$> -- Ξ, K, (TyTrFun n, Γ) T⊢ Fun f ts : TFun t' u'
          sequence [
            do
              ta <- use tsTypeAbbrevs
              mod <- use nameMod
              let unabbrev | M.null (fst ta) = "" | otherwise = " " ++ typeAbbrevBucketName
              return $ Leaf $ rule (fn_proof (mod (coreFunNameToIsabelleName f)) unabbrev),
                                        -- Ξ, K', (T, [Some t]) [ n ]T⊢ f : u
            return $ Leaf simp,         -- t' = instantiate ts t
            return $ Leaf simp,         -- u' = instantiate ts u
            consumed k env,             -- K ⊢ Γ consumed
            wellformed ks t,            -- K' ⊢ t wellformed
            allKindCorrect k ts ks      -- list_all2 (kinding K) ts K'
          ]

    _ -> error $ "ProofGen Fun: bad function call " ++ show f

  where
    findfun :: CoreFunName -> [Definition e a] -> Definition e a
    findfun f (def@(FunDef _ fn _ _ _ _):fs) | coreFunName f == fn = def
    findfun f (def@(AbsDecl _ fn _ _ _) :fs) | coreFunName f == fn = def
    findfun f (_:fs) = findfun f fs
    findfun f [] = error $ "ProofGen Fun: no such function " ++ show f

    fn_proof fn unabbrev =
      fn ++ "_typecorrect[simplified " ++ fn ++ "_type_def " ++
                          fn ++ "_typetree_def" ++ unabbrev ++ ", simplified]"

ttyping xi k (EE y (App a b) env) =
  Branch (rule "ttyping_app") <$> -- Ξ, K, Γ T⊢ App a b : y
    sequence [
      ttsplit k env (envOf a) (envOf b),   -- ttsplit K Γ [] Γ1 [] Γ2
      ttyping xi k a,                     -- Ξ, K, Γ1 T⊢ a : TFun x y
      ttyping xi k b                      -- Ξ, K, Γ2 T⊢ b : x
    ]

ttyping xi k (EE (TSum ts) (Con tag e t) env) =
  Branch (rule "ttyping_con") <$> -- Ξ, K, Γ T⊢ Con ts tag x : TSum ts'
    sequence [
      ttyping xi k e,           -- Ξ, K, Γ T⊢ x : t
      wellformed k (TSum ts),   -- K ⊢ TSum ts' wellformed
      return $ Leaf simp,       -- distinct (map fst ts)
      return $ Leaf simp        -- ts = ts'
    ]

ttyping xi k (EE u (Cast t e) env) =
  Branch (rule "ttyping_cast") <$>    -- Ξ, K, Γ T⊢ Cast τ' e : TPrim (Num τ')
    sequence [
      ttyping xi k e,                 -- Ξ, K, Γ T⊢ e : TPrim (Num τ)
      return $ Leaf simp              -- upcast_valid τ τ'
    ]

ttyping xi k (EE _ (Tuple t u) env) =
  Branch (rule "ttyping_tuple") <$> -- Ξ, K, Γ T⊢ Tuple t u : TProduct T U
    sequence [
      ttsplit k env (envOf t) (envOf u),  -- ttsplit K Γ [] Γ1 [] Γ2
      ttyping xi k t,                     -- Ξ, K, Γ1 T⊢ t : T
      ttyping xi k u                      -- Ξ, K, Γ2 T⊢ u : U
    ]

ttyping xi k (EE t' (Split a x y) env) =
  Branch (rule "ttyping_split") <$> -- Ξ, K, Γ T⊢ Split x y : t'
    sequence [
      -- follow_tt k env (envOf x) (envOf y),
      ttsplit k env (envOf x) (peel2 $ envOf y),   -- ttsplit K Γ [] Γ1 [Some t, Some u] Γ2a
      ttyping xi k x,                              -- Ξ, K, Γ1 T⊢ x : TProduct t u
      ttyping xi k y                               -- Ξ, K, Γ2a T⊢ y : t'
    ]

ttyping xi k (EE u (LetBang is a x y) env) =
  Branch (rule "ttyping_letb") <$> -- Ξ, K, Γ T⊢ LetBang is x y : u
    sequence [
      -- follow_tt k env (envOf x) (envOf y),
      ttsplit k env (envOf x) (peel $ envOf y),   -- ttsplit_bang K is Γ [] Γ1 [Some t] Γ2a
      ttyping xi k x,                             -- Ξ, K, Γ1 T⊢ x : t
      ttyping xi k y,                             -- Ξ, K, Γ2a T⊢ y : u
      kinding k (typeOf x)                        -- K ⊢ t :κ {E}
    ]

ttyping xi k (EE u (Case x _ (_,_,a) (_,_,b)) env) =
  let g   = env
      g1  = envOf x
      g2a = peel $ envOf a
      g2b = peel $ envOf b
      g2  = peel $ envOf b <|> envOf a
   in
    Branch (rule "ttyping_case") <$>  -- Ξ, K, Γ T⊢ Case x tag a b : u
      sequence [
        ttsplit k g g1 g2,    -- ttsplit K Γ [] Γ1 [] Γ2
        ttyping xi k x,       -- Ξ, K, Γ1 T⊢ x : TSum ts
        ttctxdup g2 g2a g2b,  -- ttctxdup Γ2 [Some t] Γ2a [Some (TSum (tagged_list_update tag (t, Checked) ts))] Γ2b
        return $ Leaf simp,        -- (tag, t, Unchecked) ∈ set ts
        ttyping xi k a,       -- Ξ, K, Γ2a T⊢ a : u
        ttyping xi k b        -- Ξ, K, Γ2b T⊢ b : u
      ]

ttyping xi k (EE _ (Esac x) _) =
  Branch (rule "ttyping_esac") <$>  -- Ξ, K, Γ T⊢ Esac x : t
    sequence [
      ttyping xi k x,               -- Ξ, K, Γ T⊢ x : TSum ts
      return $ Leaf simp            -- [(_, t, Unchecked)] = filter ((=) Unchecked ∘ snd ∘ snd) ts
    ]

ttyping xi k (EE t (If x a b) env) =
  let g   = env
      g1  = envOf x
      g2a = envOf a
      g2b = envOf b
      g2  = envOf b <|> envOf a
   in
    Branch (rule "ttyping_if") <$> -- Ξ, K, Γ T⊢ If x a b : t
      sequence [
        ttsplit k g g1 g2,    -- ttsplit K Γ [] Γ1 [] Γ2
        ttctxdup g2 g2a g2b,  -- ttctxdup Γ2 [] Γ2a [] Γ2b
        ttyping xi k x,       -- Ξ, K, Γ1 T⊢ x : TPrim Bool
        ttyping xi k a,       -- Ξ, K, Γ2a T⊢ a : t
        ttyping xi k b        -- Ξ, K, Γ2b T⊢ b : t
      ]

ttyping xi k (EE (TPrim t) (Op o es) env) =
  Branch (rule "ttyping_prim") <$>    -- Ξ, K, Γ T⊢ Prim oper args : TPrim t
    sequence [
      return $ Leaf simp,             -- prim_op_type oper = (ts,t)
      return $ Leaf simp,             -- ts' = map TPrim ts
      ttypingAll xi k env es          -- Ξ, K, Γ T⊢* args : ts'
    ]

ttyping xi k (EE _ (ILit _ t) env) =
  Branch (rule "ttyping_lit") <$>   -- Ξ, K, (TyTrLeaf, Γ) T⊢ Lit l : TPrim p
    sequence [
      consumed k env,               -- K ⊢ Γ consumed
      return $ Leaf simp            -- p = lit_type l
    ]

ttyping xi k (EE _ (SLit t) env) =
  Branch (rule "ttyping_lit") <$>   -- Ξ, K, (TyTrLeaf, Γ) T⊢ SLit s : TPrim String
    sequence [
      consumed k env                -- K ⊢ Γ consumed
    ]

ttyping xi k (EE _ Unit env) =
  Branch (rule "ttyping_unit") <$> -- Ξ, K, (TyTrLeaf, Γ) T⊢ Unit : TUnit
    sequence [
      consumed k env                -- K ⊢ Γ consumed
    ]

ttyping xi k (EE t (Struct fs) env) =
  Branch (rule "ttyping_struct") <$>    -- Ξ, K, Γ T⊢ Struct ts es : TRecord ts' Unboxed
    sequence [
      ttypingAll xi k env (map snd fs), -- Ξ, K, Γ T⊢* es : ts
      return $ Leaf simp,               -- ns = map fst ts'
      return $ Leaf simp,               -- ts = map (fst ∘ snd) ts'
      return $ Leaf simp,               -- list_all (λx. snd (snd x) = Present) ts'
      return $ Leaf simp,               -- distinct ns
      return $ Leaf simp                -- length ns = length ts
    ]

ttyping xi k (EE t (Member e f) env) =
  Branch (rule "ttyping_member") <$>     -- Ξ, K, Γ T⊢ Member e f : t
    sequence [
      ttyping xi k e,           -- Ξ, K, Γ T⊢ e : TRecord ts s
      kinding k (eexprType e),  -- K ⊢ TRecord ts s :κ {S}
      return $ Leaf simp,       -- f < length ts
      return $ Leaf simp        -- ts ! f = (n, t, Present)
    ]

ttyping xi k (EE t (Take a e@(EE (TRecord ts _) _ _) f e') env) =
  Branch (rule "ttyping_take") <$> -- Ξ, K, Γ T⊢ Take e f e' : u
    sequence [
      -- follow_tt k (envOf x) (envOf a) (envOf b),
      ttsplit k env (envOf e) (peel2 $ envOf e'),   -- ttsplit K Γ [] Γ1 [Some t, Some (TRecord ts' s)] Γ2a
      ttyping xi k e,                               -- Ξ, K, Γ1 T⊢ e : TRecord ts s
      return $ Leaf simp,                           -- ts' = ts[f := (n,t,taken)]
      return $ Leaf simp,                           -- sigil_perm s ≠ Some ReadOnly
      return $ Leaf simp,                           -- f < length ts
      return $ Leaf simp,                           -- ts ! f = (n, t, Present)
      wellformed k t,                               -- K ⊢ t wellformed
      kinding k (fst $ snd $ ts !! f),              -- K ⊢ t :κ k
      return $ Leaf simp,                           -- S ∈ kinding_fn K t ∨ taken = Taken
      ttyping xi k e'                               -- Ξ, K, Γ2a T⊢ e' : u
    ]

ttyping xi k (EE ty (Put e1@(EE (TRecord ts _) _ _) f e2@(EE t _ _)) env) =
  Branch (rule "ttyping_put") <$> -- Ξ, K, Γ T⊢ Put e f e' : TRecord ts' s
    sequence [
      -- follow_tt k env (envOf e) (envOf e'),
      ttsplit k env (envOf e1) (envOf e2),       -- ttsplit K Γ [] Γ1 [] Γ2
      ttyping xi k e1,                          -- Ξ, K, Γ1 T⊢ e : TRecord ts s
      return $ Leaf simp,                            -- ts' = ts[f := (n,t,Present)]
      return $ Leaf simp,                            -- sigil_perm s ≠ Some ReadOnly
      return $ Leaf simp,                            -- f < length ts
      return $ Leaf simp,                            -- ts ! f = (n, t, taken)
      wellformed k t,                             -- K ⊢ t wellformed
      return $ Leaf simp,                            -- D ∈ kinding_fn K t ∨ taken = Taken
      ttyping xi k e2                            -- Ξ, K, Γ2 T⊢ e' : t
    ]

ttyping xi k (EE _ (Promote t x) env) =
  Branch (rule "ttyping_promote") <$> -- Ξ, K, Γ T⊢ Promote t x : t
    sequence [
      subtyping k (typeOf x) t,       -- K ⊢ t' ⊑ t
      ttyping xi k x                  -- Ξ, K, Γ T⊢ x : t'
    ]

ttyping xi k _ = error "attempted to generate proof of ill-typed program"

-- return [rule_tac "ttyping_all_empty'" [("n", show . Nat.toInt . Vec.length $ g)], simp_add ["empty_def"]]
ttypingAll xi k g [] = return $
  Branch
    (rule "ttyping_all_empty") -- Ξ, K, (TyTrLeaf, Γ) T⊢* [] : []
    [
      Leaf $ simp_add ["empty_def"] -- Γ = empty n
    ]

ttypingAll xi k g (e:es) =
  let envs = foldl (<|>) (cleared g) (map envOf es)
   in
    Branch (rule "ttyping_all_cons") <$> -- Ξ, K, Γ T⊢* (e # es) : ts'
      sequence [
        ttsplit k g (envOf e) envs,   -- ttsplit K Γ [] Γ1 [] Γ2
        return (Leaf simp),           -- ts' = (t # ts)
        ttyping xi k e,               -- Ξ, K, Γ1 T⊢ e : t
        ttypingAll xi k envs es       -- Ξ, K, Γ2 T⊢* es : ts
      ]

allVars :: [Expr a b c d] -> Bool
allVars (Variable _ : vs) = allVars vs
allVars [] = True
allVars _ = False

-- typing :: Xi a -> Vec t Kind -> EnvExpr t v a -> State TypingSubproofs [Tactic]
-- typing xi k (EE t (Variable i) env) = tacSequence [
--   return $ [rule "typing_var"],           -- Ξ, K, Γ ⊢ Var i : t if
--   weakens k env (singleton (fst i) env),  -- K ⊢ Γ ↝w singleton (length Γ) i t
--   return [simp]                           -- i < length Γ
--   ]

-- typing xi k (EE t' (Fun f ts _) env) = case findfun (coreFunNameToIsabelleName f) xi of
--     AbsDecl _ _ ks' t u ->
--       let ks = fmap snd ks' in tacSequence [
--         return [rule "typing_afun'"],  -- Ξ, K, Γ ⊢ AFun f ts : t' if
--         do ta <- use tsTypeAbbrevs
--            mod <- use nameMod
--            let unabbrev | M.null (fst ta) = ""
--                         | otherwise = "[unfolded " ++ typeAbbrevBucketName ++ "]"
--            return [simp_add ["\\<Xi>_def", mod (coreFunNameToIsabelleName f) ++ "_type_def" ++ unabbrev]],  -- Ξ f = (K', t, u)
--         allKindCorrect k ts ks,    -- list_all2 (kinding K) ts K'
--         return [simp],             -- instantiate ts (TFun t u)
--         wellformed ks (TFun t u),  -- K' ⊢ TFun t u wellformed
--         consumed k env             -- K ⊢ Γ consumed
--         ]

--     FunDef _ _ ks' t u _ ->
--       let ks = fmap snd ks' in tacSequence [
--         return [rule "typing_fun'"],  -- Ξ, K, Γ ⊢ Fun f ts : t' if
--         do ta <- use tsTypeAbbrevs
--            mod <- use nameMod
--            let unabbrev | M.null (fst ta) = "" | otherwise = " " ++ typeAbbrevBucketName
--            return [rule (fn_proof (mod (coreFunNameToIsabelleName f)) unabbrev)],  -- Ξ, K', [Some t] ⊢ f : u
--         allKindCorrect k ts ks,  -- list_all2 (kinding K) ts K'
--         return [simp],           -- t' = instantiate ts (TFun t u)
--         wellformed ks t,         -- K' ⊢ t wellformed
--         consumed k env           -- K ⊢ Γ consumed
--         ]

--     _ -> error $ "ProofGen Fun: bad function call " ++ show f

--   where findfun f (def@(FunDef _ fn _ _ _ _):fs) | f == fn = def
--         findfun f (def@(AbsDecl _ fn _ _ _) :fs) | f == fn = def
--         findfun f (_:fs) = findfun f fs
--         findfun f [] = error $ "ProofGen Fun: no such function " ++ show f

--         fn_proof fn unabbrev =
--           fn ++ "_typecorrect[simplified " ++ fn ++ "_type_def " ++
--                               fn ++ "_typetree_def" ++ unabbrev ++ ", simplified]"

-- typing xi k (EE y (App a b) env) = tacSequence [
--   return [rule "typing_app"],        -- Ξ, K, Γ ⊢ App a b : y if
--   splits k env (envOf a) (envOf b),  -- K ⊢ Γ ↝ Γ1 | Γ2
--   typing xi k a,                     -- Ξ, K, Γ1 ⊢ a : TFun x y
--   typing xi k b                      -- Ξ, K, Γ2 ⊢ b : x
--   ]

-- typing xi k (EE (TSum ts) (Con tag e t) env) = tacSequence [
--   return [rule "typing_con"],            -- Ξ, K, Γ ⊢ Con ts tag x : TSum ts if
--   typing xi k e,                         -- Ξ, K, Γ ⊢ x : t
--   return [simp],                         -- (tag,t,False) ∈ set ts
--   wellformedAll k (map (fst . snd) ts),  -- K ⊢* (map (fst ∘ snd) ts) wellformed
--   return (distinct (map fst ts)),        -- distinct (map fst ts)
--   return [simp],                         -- map fst ts = map fst ts'
--   return [simp],                         -- map (fst ∘ snd) ts = map (fst ∘ snd) ts'
--   return [simp]                          -- list_all2 (λx y. snd (snd y) ⟶ snd (snd x)) ts ts'
--   ]

-- typing xi k (EE u (Cast t e) env) = __todo "typing: Cast"
--   -- \ | EE (TPrim pt) _ _ <- e, TPrim pt' <- ty, pt /= Boolean = tacSequence [
--   -- \   return [rule "typing_cast"],   -- Ξ, K, Γ ⊢ Cast τ' e : TPrim (Num τ') if
--   -- \   typing xi k e,                 -- Ξ, K, Γ ⊢ e : TPrim (Num τ)
--   -- \   return [simp]                  -- upcast_valid τ τ'
--   -- \   ]

-- typing xi k (EE _ (Tuple t u) env) = tacSequence [
--   return [rule "typing_tuple"],      -- Ξ, K, Γ ⊢ Tuple t u : TProduct T U if
--   splits k env (envOf t) (envOf u),  -- K ⊢ Γ ↝ Γ1 | Γ2
--   typing xi k t,                     -- Ξ, K, Γ1 ⊢ t : T
--   typing xi k u                      -- Ξ, K, Γ2 ⊢ u : U
--   ]

-- typing xi k (EE t' (Split a x y) env) = tacSequence [
--   return [rule "typing_split"],              -- Ξ, K, Γ ⊢ Split x y : t' if
--   splits k env (envOf x) (peel2 $ envOf y),  -- K ⊢ Γ ↝ Γ1 | Γ2
--   typing xi k x,                             -- Ξ, K, Γ1 ⊢ x : TProduct t u
--   typing xi k y                              -- Ξ, K, (Some t)#(Some u)#Γ2 ⊢ y : t'
--   ]

-- typing xi k (EE u (Let a x y) env) = tacSequence [
--   return [rule "typing_let"],               -- Ξ, K, Γ ⊢ Let x y : u if
--   splits k env (envOf x) (peel $ envOf y),  -- K ⊢ Γ ↝ Γ1 | Γ2
--   typing xi k x,                            -- Ξ, K, Γ1 ⊢ x : t
--   typing xi k y                             -- Ξ, K, (Some t # Γ2) ⊢ y : u
--   ]

-- typing xi k (EE u (LetBang is a x y) env) = tacSequence [
--   return [rule "typing_letb"],                    -- Ξ, K, Γ ⊢ LetBang is x y : u if
--   error "split_bang: should be ttyping LetBang",  -- split_bang K is Γ Γ1 Γ2
--   typing xi k x,                                  -- Ξ, K, Γ1 ⊢ x : t
--   typing xi k y,                                  -- Ξ, K, (Some t # Γ2) ⊢ y : u
--   kinding k (typeOf x),                           -- K ⊢ t :κ k
--   return [simp]                                   -- E ∈ k
--   ]

-- typing xi k (EE u (Case x _ (_,_,a) (_,_,b)) env) = tacSequence [
--   return [rule "typing_case"],  -- Ξ, K, Γ ⊢ Case x tag a b : u if
--   splits k env (envOf x) (peel $ envOf b <|> envOf a),  -- K ⊢ Γ ↝ Γ1 | Γ2
--   typing xi k x,                -- Ξ, K, Γ1 ⊢ x : TSum ts
--   return [simp],                -- (tag, (t,False)) ∈ set ts
--   typing xi k a,                -- Ξ, K, (Some t # Γ2) ⊢ a : u
--   typing xi k b                 -- Ξ, K, (Some (TSum (tagged_list_update tag (t, True) ts)) # Γ2) ⊢ b : u
--   ]

-- typing xi k (EE _ (Esac x) _) = tacSequence [
--   return [rule "typing_esac"],  -- Ξ, K, Γ ⊢ Esac x : t if
--   typing xi k x,                -- Ξ, K, Γ ⊢ x : TSum ts
--   return [simp]                 -- [(_, (t,False))] = filter (HOL.Not ∘ snd ∘ snd) ts
--   ]

-- typing xi k (EE t (If x a b) env) = tacSequence [
--   return [rule "typing_if"],                     -- Ξ, K, Γ ⊢ If x a b : t if
--   splits k env (envOf x) (envOf a <|> envOf b),  -- K ⊢ Γ ↝ Γ1 | Γ2
--   typing xi k x,                                 -- Ξ, K, Γ1 ⊢ x : TPrim Bool
--   typing xi k a,                                 -- Ξ, K, Γ2 ⊢ a : t
--   typing xi k b                                  -- Ξ, K, Γ2 ⊢ b : t
--   ]

-- typing xi k (EE (TPrim t) (Op o es) env) = tacSequence [
--   return [rule "typing_prim'"],  -- Ξ, K, Γ ⊢ Prim oper args : TPrim t if
--   return [simp],                 -- prim_op_type oper = (ts,t)
--   return [simp],                 -- ts' = map TPrim ts;
--   typingAll xi k env es          -- Ξ, K, Γ ⊢* args : ts'
--   ]

-- typing xi k (EE _ (ILit _ t) env) = tacSequence [
--   return [rule "typing_lit'"],  -- Ξ, K, Γ ⊢ Lit l : TPrim t if
--   consumed k env,               -- K ⊢ Γ consumed
--   return [simp]                 -- t = lit_type l
--   ]

-- typing xi k (EE _ (SLit t) env) = tacSequence [
--   return [rule "typing_lit'"],  -- Ξ, K, Γ ⊢ Lit l : TPrim t if
--   consumed k env,               -- K ⊢ Γ consumed
--   return [simp]                 -- t = lit_type l
--   ]

-- typing xi k (EE _ Unit env) = tacSequence [
--   return [rule "typing_unit"],  -- Ξ, K, Γ ⊢ Unit : TUnit if
--   consumed k env                -- K ⊢ Γ consumed
--   ]

-- typing xi k (EE t (Struct fs) env) = tacSequence [
--   return [rule "typing_struct'"],    -- Ξ, K, Γ ⊢ Struct ts es : TRecord ts' Unboxed
--   typingAll xi k env (map snd fs),   -- Ξ, K, Γ ⊢* es : ts
--   return [simp]                      -- ts' = zip ts (replicate (length ts) False)
--   ]

-- typing xi k (EE t (Member e f) env) = tacSequence [
--   return [rule "typing_member"],   -- Ξ, K, Γ ⊢ Member e f : t if
--   typing xi k e,                   -- Ξ, K, Γ ⊢ e : TRecord ts s
--   kinding k (eexprType e),         -- K ⊢ TRecord ts s :κ k (* k introduced *)
--   return [simp, simp, simp]        -- S ∈ k;  f < length ts; ts ! f = (t, False)
--   ]

-- typing xi k (EE u (Take a e@(EE (TRecord ts _) _ _) f e') env) = tacSequence [
--   return [rule "typing_take"],                -- Ξ, K, Γ ⊢ Take e f e' : u if
--   splits k env (envOf e) (peel2 $ envOf e'),  -- K ⊢ Γ ↝ Γ1 | Γ2
--   typing xi k e,                              -- Ξ, K, Γ1 ⊢ e : TRecord ts s
--   return [simp, simp, simp],                  -- s ≠ ReadOnly; f < length ts; ts ! f = (t, False) (* instantiates t *)
--   kinding k (fst $ snd $ ts !! f),            -- K ⊢ t :κ k
--   return (sharableOrTaken f (envOf e')),      -- S ∈ k ∨ taken (* instantiates taken *)
--   return [simp],
--   typing xi k e'                              -- Ξ, K, (Some t # Some (TRecord (ts [f := (t,taken)]) s) # Γ2) ⊢ e' : u
--   ]

-- typing xi k (EE ty (Put e1@(EE (TRecord ts _) _ _) f e2@(EE t _ _)) env) = tacSequence [
--   return [rule "typing_put'"],                        -- Ξ, K, Γ ⊢ Put e f e' : TRecord ts' s if
--   splits k env (envOf e1) (envOf e2),                 -- K ⊢ Γ ↝ Γ1 | Γ2
--   typing xi k e1,                                     -- Ξ, K, Γ1 ⊢ e : TRecord ts s
--   return [simp, simp],                                -- s ≠ ReadOnly; f < length ts;
--   return [simp_del ["Product_Type.prod.inject"]],     -- ts ! f = (t, taken)
--   kinding k t,                                        -- K ⊢ t :κ k
--   return (destroyableOrTaken (snd $ snd $ ts !! f)),  -- D ∈ k ∨ taken
--   typing xi k e2,                                     -- Ξ, K, Γ2 ⊢ e' : t
--   return [simp]                                       -- ts' = (ts [f := (t,False)])
--   ]

-- typing xi k (EE _ (Promote ty e) env) = typing xi k e  -- FIXME: also requires a proof for subtyping / zilinc

-- typing xi k _ = error "attempted to generate proof of ill-typed program"

-- typingAll :: Xi a -> Vec t Kind -> Vec v (Maybe (Type t)) -> [EnvExpr t v a] -> State TypingSubproofs [Tactic]
-- -- Γ = empty n ⟹  Ξ, K, Γ ⊢* [] : []
-- typingAll xi k g [] = return [rule_tac "typing_all_empty'" [("n", show . Nat.toInt . Vec.length $ g)],
--                               simp_add ["empty_def"]]
-- -- Ξ, K, Γ ⊢* (e # es) : (t # ts)
-- typingAll xi k g (e:es) =
--   let envs = foldl (<|>) (cleared g) (map envOf es) in tacSequence [
--     return [rule "typing_all_cons"], splits k g (envOf e) envs, typing xi k e, typingAll xi k envs es
--     ]

kinding :: Vec t Kind -> Type t -> State TypingSubproofs (HintTree Tactic Tactic)
kinding k t = Branch (rule "kindingI") <$>
  sequence [
    wellformed k t,
    return $ Leaf simp
  ]

subtyping :: Vec t Kind -> Type t -> Type t -> State TypingSubproofs (HintTree Tactic Tactic)
subtyping k (TVar _)           (TVar _)         = return $
  Branch (rule "subtyping_tvar") [ Leaf simp ]
subtyping k (TVarBang _)       (TVarBang _)     = return $
  Branch (rule "subtyping_tvarb") [ Leaf simp ]
subtyping k (TUnit)            (TUnit)          = return $
  Branch (rule "subtyping_tunit") []
subtyping k (TProduct t1 u1)   (TProduct t2 u2) =
  Branch (rule "subtyping_tprod") <$>
    sequence [
      subtyping k t1 t2,
      subtyping k u1 u2
    ]
subtyping k (TSum ts1)         (TSum ts2)       =
  Branch (rule "subtyping_tsum") <$>  -- K ⊢ TSum ts1 ⊑ TSum ts2
    sequence [
      __todo "subtyping: recursive goal in tsum", -- list_all2 (λp1 p2. fst p1 = fst p2 ∧ K ⊢ fst (snd p1) ⊑ fst (snd p2) ∧ snd (snd p1) ≤ snd (snd p2)) ts1 ts2
      return $ Leaf simp,                         -- ; distinct (map fst ts1)
      return $ Leaf simp                          -- ; distinct (map fst ts2)
    ]
subtyping k (TFun t1 u1)       (TFun t2 u2)     =
  Branch (rule "subtyping_tfun") <$>
    sequence [
      subtyping k t2 t1,
      subtyping k u1 u2
    ]
subtyping k (TRecord ts1 s1)   (TRecord ts2 s2) =
  Branch (rule "subty_trecord") <$>  -- K ⊢ TRecord ts1 s1 ⊑ TRecord ts2 s2
    sequence [
      __todo "subtyping: recursive goal in trecord",  -- list_all2 (λp1 p2. fst p1 = fst p2 ∧ K ⊢ fst (snd p1) ⊑ fst (snd p2) ∧ (if K ⊢ fst (snd p1) :κ {D} then snd (snd p1) ≤ snd (snd p2) else snd (snd p1) = snd (snd p2))) ts1 ts2
      return $ Leaf simp,                             -- ; distinct (map fst ts1)
      return $ Leaf simp,                             -- ; distinct (map fst ts2)
      return $ Leaf simp
    ]
subtyping k (TPrim _)          (TPrim _)        = return $
  Branch (rule "subtyping_tprim") [ Leaf simp ]
subtyping k (TString)          (TString)        = return $
  Branch (rule "subtyping_tprim") [ Leaf simp ]
subtyping k (TCon n1 ts1 s1)   (TCon n2 ts2 s2) = return $
  Branch (rule "subtyping_tcon") [Leaf simp, Leaf simp, Leaf simp]
subtyping _ _ _ = __impossible "subtyping: tried to subtype incompatible types"

-- kind :: Vec t Kind -> Type t -> Kind -> State TypingSubproofs [Tactic]
-- kind ks (TVar v)         k = return [simp, simp]
-- kind ks (TVarBang v)     k = return [simp, simp]
-- kind ks (TUnit)          k = return []
-- kind ks (TProduct t1 t2) k = tacSequence [kinding' ks t1 k, kinding' ks t2 k]
-- kind ks (TSum ts)        k = tacSequence [kindingVariant ks (map snd ts) k, return [simp, simp], kindingAll ks (map (fst . snd) ts) k]
-- kind ks (TFun ti to)     k = tacSequence [kinding ks ti, kinding ks to]
-- kind ks (TRecord ts s)   k = tacSequence [kindingRecord ks (map snd ts) k, return [simp]]
-- kind ks (TPrim i)        k = return []
-- kind ks (TString)        k = return []
-- kind ks (TCon n ts s)    k = tacSequence [kindingAll ks ts k, return [simp]]

kindingAll :: Vec t Kind -> [Type t] -> Kind -> State TypingSubproofs [Tactic]
kindingAll _ _ k = return [simp_add ["kinding_def", "kinding_all_def", "kinding_variant_def", "kinding_record_def"]]

kindingRecord :: Vec t Kind -> [(Type t, Bool)] -> Kind -> State TypingSubproofs [Tactic]
kindingRecord _ _ k = return [simp_add ["kinding_def", "kinding_all_def", "kinding_variant_def", "kinding_record_def"]]

kindingVariant :: Vec t Kind -> [(Type t, Bool)] -> Kind -> State TypingSubproofs [Tactic]
kindingVariant _ _ k = return [simp_add ["kinding_def", "kinding_all_def", "kinding_variant_def", "kinding_record_def"]]

allKindCorrect :: Vec t' Kind -> [Type t'] -> Vec t Kind -> State TypingSubproofs (HintTree Tactic Tactic)
allKindCorrect k (t : ts) (Cons _ ks') =
  Branch (rule "list_all2_cons") <$>
    sequence [
      kinding k t,
      allKindCorrect k ts ks'
    ]
allKindCorrect _ [] Nil = return $ Branch (rule "list_all2_nil") []
allKindCorrect _ _ _ = error "allKindCorrect: mismatched list lengths"
-- do
--   let k' = cvtToList k
--       ts' = map stripType ts
--       ks' = cvtToList ks
--   ta <- use tsTypeAbbrevs
--   akmap <- use subproofAllKindCorrect
--   case M.lookup (k', ts', ks') akmap of
--     Nothing -> do mod <- use nameMod
--                   let prop = mkApp (mkId "list_all2")
--                                [mkApp (mkId "kinding") [mkList (map deepKind k')], mkList (map (deepType mod ta) ts), mkList (map deepKind ks')]
--                   tac <- tacSequence [return [Simplifier [] [NthThm "HOL.simp_thms" 25, NthThm "HOL.simp_thms" 26]],
--                                       allKindCorrect' k ts ks]
--                   proofId <- newSubproofId
--                   subproofAllKindCorrect %= M.insert (k', ts', ks') (proofId, (False, prop), tac)
--                   return [rule $ typingSubproofPrefix ++ show proofId]
--     Just (proofId, _, _) -> return [rule $ typingSubproofPrefix ++ show proofId]

-- allKindCorrect' :: Vec t' Kind -> [Type t'] -> Vec t Kind -> State TypingSubproofs [Tactic]
-- allKindCorrect' kind (t:ts) (Cons k ks)
--   = tacSequence [return (breakConj ts), kinding' kind t k, allKindCorrect' kind ts ks]
-- allKindCorrect' _ [] Nil = return []
-- allKindCorrect' _ _ _ = error "kind mismatch"

-- follow_tt :: Vec t Kind -> Vec v (Maybe (Type t)) -> Vec vx (Maybe (Type t))
--           -> Vec vy (Maybe (Type t)) -> State TypingSubproofs (HintTree Hints Hints)
-- follow_tt k env env_x env_y = return $
--   map (kindingHint k) new
--   where
--     l = Nat.toInt (Vec.length env)
--     n_x = take (Nat.toInt (Vec.length env_x) - l) (cvtToList env_x)
--     n_y = take (Nat.toInt (Vec.length env_y) - l) (cvtToList env_y)
--     new = catMaybes (n_x ++ n_y)

ttsplit :: Vec t Kind -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> State TypingSubproofs (HintTree Tactic Tactic)
ttsplit k ga g1a g2a =
  Branch (rule "ttsplitI") <$> -- ttsplit K (TyTrSplit sps xs T1 ys T2, Γa) xsa (T1, xs') ysa (T2, ys')
    sequence [
      ttsplit_inner k ga g1a g2a,  -- "ttsplit_inner K sps Γa Γ1a Γ2a"
      return $ Leaf simp,             -- "xsa = xs"
      return $ Leaf simp,             -- "ysa = ys"
      return $ Leaf simp,             -- "xs' = xs @ Γ1a"
      return $ Leaf simp,             -- "ys' = ys @ Γ2a"
      return $ Leaf simp              -- "list_all (λs. s ≠ Some TSK_NS) sps"
    ]

ttsplit_inner :: Vec t Kind -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> State TypingSubproofs (HintTree Tactic Tactic)
ttsplit_inner k (Cons t ga) (Cons t1 g1a) (Cons t2 g2a) =
  Branch (rule "ttsplit_inner_cons") <$>
    sequence [
      return $ Leaf $ simp_add ["tsk_split_comp.simps"],
      ttsplit_inner k ga g1a g2a
    ]
ttsplit_inner k Nil Nil Nil = return $ Branch (rule "ttsplit_inner_nil") []

ttctxdup :: Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> State TypingSubproofs (HintTree Tactic Tactic)
ttctxdup g g1 g2 = return $
  Branch (rule "ttctxdupI") [ Leaf simp, Leaf simp ]

-- K ⊢ τ wellformed ≡ ∃k. K ⊢ τ :κ k
wellformed :: Vec t Kind -> Type t -> State TypingSubproofs (HintTree Tactic Tactic)
wellformed ks t = return $ Leaf simp

-- K ⊢ Γ consumed ≡ K ⊢ Γ ↝w empty (length Γ)
consumed :: Vec t Kind -> Vec v (Maybe (Type t)) -> State TypingSubproofs (HintTree Tactic Tactic)
consumed k (Cons t g) =
  Branch (rule "is_consumed_nil") <$>
    sequence [
      return $ Leaf $ simp_add ["weakening_comp.simps"], -- TODO has a wellformed/kinding in it
      consumed k g
    ]
consumed k Nil = return $
  Branch (rule "is_consumed_cons") []

-- K ⊢ Γ ↝w Γ'
weakens :: Vec t Kind -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> State TypingSubproofs (HintTree Tactic Tactic)
weakens k (Cons t g) (Cons t' g') =
  Branch (rule "weakening_cons") <$>
    sequence [
      return $ Leaf $ simp_add ["weakening_comp.simps"], -- TODO has a wellformed/kinding in it
      weakens k g g'
    ]
weakens k Nil Nil = return $
  Branch (rule "weakening_nil") []

--  do
--   let k' = cvtToList k
--       [gl, gl'] = map cvtToList [g, g']
--       [glt, glt'] = map (map (fmap stripType)) [gl, gl']
--   ta <- use tsTypeAbbrevs
--   if not cacheWeakeningProofs
--     then do proofIds <- kindingAssms (zip gl gl')
--             thms <- mapM (thmTypeAbbrev . (typingSubproofPrefix ++) . show) (nub proofIds)
--             return [simp_add ["empty_def"], WeakeningTac thms]
--     else do
--     wmap <- use subproofWeakens
--     case M.lookup (k', glt, glt') wmap of
--       Nothing -> do mod <- use nameMod
--                     let prop = mkApp (mkId "weakening")
--                                  [mkList (map deepKind k'),
--                                   mkList (map (deepMaybeTy mod ta) gl),
--                                   mkList (map (deepMaybeTy mod ta) gl')]
--                     proofIds <- kindingAssms (zip gl gl')
--                     thms <- mapM (thmTypeAbbrev . (typingSubproofPrefix ++) . show) (nub proofIds)
--                     proofId <- newSubproofId
--                     subproofWeakens %= M.insert (k', glt, glt') (proofId, (False, prop), [WeakeningTac thms])
--                     thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
--                     return [simp_add ["empty_def"], RuleTac thm]
--       Just (proofId, _, _) -> do thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
--                                  return [simp_add ["empty_def"], RuleTac thm]
--   where kindingAssms [] = return []
--         kindingAssms ((Just t, _):xs) = liftM2 (:) (kindingRaw k t) (kindingAssms xs)
--         kindingAssms (_:xs) = kindingAssms xs

breakConj :: [t] -> [Tactic]
breakConj (x:xs) = [rule "conjI"]
breakConj []     = []

takeTaken :: FieldIndex -> Vec v (Maybe (Type t)) -> Bool
takeTaken f (Cons x (Cons (Just (TRecord ts _)) _)) = snd $ snd (ts!!f)
takeTaken _ _ = error "invalid call to takeTaken"

sharableOrTaken :: FieldIndex -> Vec v (Maybe (Type t)) -> [Tactic]
sharableOrTaken f e | takeTaken f e = [rule_tac "disjI2" [("Q", "True")], simp]
                    | otherwise     = [rule "disjI1", simp]

destroyableOrTaken True  = [rule_tac "disjI2" [("Q", "True")], simp]
destroyableOrTaken False = [rule "disjI1", simp]

singleton :: Fin v -> Vec v (Maybe a) -> Vec v (Maybe a)
singleton v env = update (cleared env) v (env `at` v)

mostGeneralKind :: Vec t Kind -> Type t -> Kind
mostGeneralKind k (TVar v)         = k `at` v
mostGeneralKind k (TVarBang v)     = k0
mostGeneralKind k (TUnit)          = mempty
mostGeneralKind k (TProduct t1 t2) = mostGeneralKind k t1 <> mostGeneralKind k t2
mostGeneralKind k (TSum ts)        = foldl (<>) mempty $ map (mostGeneralKind k . fst . snd) ts
mostGeneralKind k (TFun ti to)     = mempty
mostGeneralKind k (TRecord ts s)   = foldl (<>) (sigilKind s) $ map (mostGeneralKind k) [t | (_, (t, b)) <- ts, not b]
mostGeneralKind k (TPrim i)        = mempty
mostGeneralKind k (TString)        = mempty
mostGeneralKind k (TCon n ts s)    = foldl (<>) (sigilKind s) $ map (mostGeneralKind k) ts

kindRule :: Type t -> String
kindRule TVar     {} = "kind_tvar"
kindRule TVarBang {} = "kind_tvarb"
kindRule TUnit       = "kind_tunit"
kindRule TProduct {} = "kind_tprod"
kindRule TSum     {} = "kind_tsum"
kindRule TFun     {} = "kind_tfun"
kindRule TRecord  {} = "kind_trec"
kindRule TPrim    {} = "kind_tprim"
kindRule TString     = "kind_tprim"
kindRule TCon     {} = "kind_tcon"

envOf = eexprEnv
typeOf = eexprType

peel :: Vec ('Suc v) t -> Vec v t
peel (Cons x xs) = xs

peel2 = peel . peel

(<|>) :: Vec v (Maybe a) -> Vec v (Maybe a) -> Vec v (Maybe a)
(<|>) (Cons Nothing xs)  (Cons Nothing ys)  = Cons Nothing  (xs <|> ys)
(<|>) (Cons _ xs)        (Cons (Just y) ys) = Cons (Just y) (xs <|> ys)
(<|>) (Cons (Just x) xs) (Cons _ ys)        = Cons (Just x) (xs <|> ys)
(<|>) Nil Nil = Nil
#if __GLASGOW_HASKELL__ < 711
(<|>) _ _ = __ghc_t4139 "ProofGen.<|>"
#endif

cleared :: Vec a (Maybe t) -> Vec a (Maybe t)
cleared = emptyvec . Vec.length
    where emptyvec :: SNat a -> Vec a (Maybe t)
          emptyvec (SSuc n) = Cons Nothing $ emptyvec n
          emptyvec (SZero)  = Nil

deepKindStr (K e s d) = "{" ++ intercalate "," [flag | (f, flag) <- zip [e, s, d] ["E", "S", "D"], f] ++ "}"

deepMaybe :: Maybe Term -> Term
deepMaybe Nothing = mkId "None"
deepMaybe (Just x) = mkApp (mkId "Some") [x]

deepMaybeTy :: NameMod -> TypeAbbrevs -> Maybe (Type t) -> Term
deepMaybeTy mod ta = deepMaybe . fmap (deepType mod ta)


