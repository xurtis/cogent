-- |
-- Module      : Minigent.TC.ConstraintGen
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The constraint generator portion of the type inference.
--
-- May be used qualified or unqualified.
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Minigent.TC.ConstraintGen (CG, runCG, cg, cgFunction) where

import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Row as Row
import Minigent.Fresh
import Minigent.Environment

import Control.Monad.Reader
import Control.Monad.State

import qualified Data.Map as M
import Data.Stream (Stream)

-- | A monad that is a combination of a state monad for the current type context,
--   a reader monad for the global environments, and fresh variables.
newtype CG a = CG (StateT (Context Type) (ReaderT GlobalEnvironments (Fresh VarName)) a)
        deriving ( Monad, Applicative, Functor, MonadState (Context Type)
                 , MonadFresh VarName, MonadReader GlobalEnvironments
                 )

-- | Given an initial context and global environments, run a 'CG' computation.
runCG :: CG a -> Context Type -> GlobalEnvironments -> Fresh VarName a
runCG (CG x) ctx glb = runReaderT (evalStateT x ctx) glb

-- | The constraint generation relation for expressions as given in the language
--   definition.
--
--   @cg e tau@ returns @(e', c)@, where @e'@ is an annotated version of @e@ that contains
--   unknowns (unification variables) that, when substituted by a satisfying assignment to @c@,
--   produces a well-typed epxression.
cg :: Expr -> Type -> CG (Expr, Constraint)
cg e tau = case e of

  (Var v) -> do
    (rho, c) <- lookupVar v
    withSig (Var v, c :&: rho :< tau)

  (Sig e1 tau') -> do
    (e1', c) <- cg e1 tau'
    withSig (Sig e1' tau', c :&: tau' :< tau)

  (Apply e1 e2) -> do
    alpha <- UnifVar <$> fresh
    (e1', c1) <- cg e1 (Function alpha tau)
    (e2', c2) <- cg e2 alpha
    withSig (Apply e1' e2', c1 :&: c2)

  (Let x e1 e2) -> do
    alpha <- UnifVar <$> fresh
    (e1', c1) <- cg e1 alpha
    modify (push (x, alpha))
    (e2', c2) <- cg e2 tau
    used <- topUsed <$> get
    let c3 = if not used then Drop alpha else Sat
    modify pop
    withSig (Let x e1' e2', c1 :&: c2 :&: c3)

  (Literal l) -> do
    let c = case l of
              BoolV _ -> PrimType Bool :< tau
              UnitV   -> PrimType Unit :< tau
              IntV  l -> l :<=: tau
    withSig (e, c)

  (If e1 e2 e3) -> do
    (e1', c1) <- cg e1 (PrimType Bool)
    g2 <- get
    (e2', c2) <- cg e2 tau
    g3 <- get
    put g2
    (e3', c3) <- cg e3 tau
    g3' <- get
    let (as, g4) = reconcile g3 g3'
        c4       = conjunction (map Drop as)
    put g4
    withSig (If e1' e2' e3', c1 :&: c2 :&: c3 :&: c4)

  (PrimOp Not [e]) -> do
    (e', c) <- cg e (PrimType Bool)
    withSig (PrimOp Not [e'], c :&: PrimType Bool :< tau)

  (PrimOp o [e1,e2])
    | o `elem` boolOps -> do
      (e1', c1) <- cg e1 (PrimType Bool)
      (e2', c2) <- cg e2 (PrimType Bool)
      withSig (PrimOp o [e1', e2'], c1 :&: c2 :&: PrimType Bool :< tau)
    | o `elem` compOps -> do
        alpha <- UnifVar <$> fresh
        (e1', c1) <- cg e1 alpha
        (e2', c2) <- cg e2 alpha
        withSig (PrimOp o [e1', e2'], 0 :<=: alpha :&: c1 :&: c2 :&: PrimType Bool :< tau)
    | otherwise -> do
        (e1', c1) <- cg e1 tau
        (e2', c2) <- cg e2 tau
        withSig (PrimOp o [e1', e2'], 0 :<=: tau :&: c1 :&: c2)

  (TypeApp f ts) -> do
    Just (Forall vs cs t) <- M.lookup f . types <$> ask
    as <- freshes (length vs - length ts)
    let ts'   = ts ++ map UnifVar as
        subst = zip vs ts'
        cs'   = map (constraintTypes (traverseType (substTVs subst))) cs
    withSig (TypeApp f ts', traverseType (substTVs subst) t :< tau :&: conjunction cs')

  (Con n e) -> do
    alpha <- UnifVar <$> fresh
    row <- Row.incomplete [Entry n alpha False]
    (e', c) <- cg e alpha
    withSig (Con n e', Variant row :< tau :&: c)

  (Case e1 k x e2 y e3) -> do
    beta <- UnifVar <$> fresh
    row <- Row.incomplete [Entry k beta False]
    (e1', c1) <- cg e1 (Variant row)
    g2 <- get
    modify (push (x, beta))
    (e2', c2) <- cg e2 tau
    xUsed <- topUsed <$> get
    let c6 = if xUsed then Sat else Drop beta
    modify pop
    g3 <- get
    put g2
    let row' = Row.take k row
    modify (push (y, Variant row'))
    (e3', c3) <- cg e3 tau
    yUsed <- topUsed <$> get
    let c7 = if yUsed then Sat else Drop (Variant row')
    modify pop
    g3' <- get
    let (as, g4) = reconcile g3 g3'
        c4       = conjunction (map Drop as)
    put g4
    withSig (Case e1' k x e2' y e3', c1 :&: c2 :&: c3 :&: c4 :&: c6 :&: c7)


  (Esac e1 k x e2) -> do
    beta <- UnifVar <$> fresh
    row <- Row.incomplete [Entry k beta False]
    (e1', c1) <- cg e1 (Variant row)
    modify (push (x, beta))
    (e2', c2) <- cg e2 tau
    xUsed <- topUsed <$> get
    let c4 = if xUsed then Sat else Drop beta
        c3 = Exhausted (Variant (Row.take k row))
    modify pop
    withSig (Esac e1' k x e2', c1 :&: c2 :&: c3 :&: c4)

  (LetBang ys x e1 e2) -> do
    alpha <- UnifVar <$> fresh
    (rhos, g1) <- factor ys <$> get
    put (fmap Bang rhos <> g1)
    (e1', c1) <- cg e1 alpha
    (bangRhos', g2) <- factor ys <$> get
    let c3 = conjunction (map Drop (unused bangRhos'))
    put (rhos <> g2)
    modify (push (x, alpha))
    (e2', c2) <- cg e2 tau
    xUsed <- topUsed <$> get
    let c5 = if xUsed then Sat else Drop alpha
    modify pop
    rhos' <- fst . factor ys <$> get
    let c4 = conjunction (map Drop (unused rhos'))
        c6 = Escape alpha
    withSig (LetBang ys x e1' e2', c1 :&: c2 :&: c3 :&: c4 :&: c5 :&: c6)

  (Member e f) -> do
    row <- Row.incomplete [Entry f tau False]
    sigil <- fresh
    let alpha = Record row (UnknownSigil sigil)
    (e', c1) <- cg e alpha
    let c2 = Drop (Record (Row.take f row) (UnknownSigil sigil))
    withSig (Member e' f, c1 :&: c2)

  (Take x f y e1 e2) -> do
    beta <- UnifVar <$> fresh
    row <- Row.incomplete [Entry f beta False]
    sigil <- fresh
    let alpha = Record row (UnknownSigil sigil)

    (e1', c1) <- cg e1 alpha
    modify (push (y, beta))
    modify (push (x, Record (Row.take f row) (UnknownSigil sigil)))
    (e2', c2) <- cg e2 tau
    xUsed <- topUsed <$> get
    let c3 = if xUsed then Sat else Drop (Record (Row.take f row) (UnknownSigil sigil))
    modify pop
    yUsed <- topUsed <$> get
    let c4 = if yUsed then Sat else Drop beta
    modify pop
    withSig (Take x f y e1' e2', c1 :&: c2 :&: c3 :&: c4)

  (Put e1 f e2) -> do
    beta <- UnifVar <$> fresh
    row  <- Row.incomplete [Entry f beta True]
    sigil <- fresh
    let alpha = Record row (UnknownSigil sigil)
    (e1', c1) <- cg e1 alpha
    (e2', c2) <- cg e2 beta
    let c3 = Record (Row.put f row) (UnknownSigil sigil) :< tau
    withSig (Put e1' f e2', c1 :&: c2 :&: c3)

  (Struct fs) -> do
    (fs', ts, cs) <- cgStruct fs
    withSig (Struct fs', conjunction cs :&: Record (Row.fromList ts) Unboxed :< tau )

  where

    cgStruct :: [(FieldName, Expr)] -> CG ([(FieldName, Expr)], [Entry], [Constraint])
    cgStruct [] = return ([], [], [])
    cgStruct ((f,e):fs) = do
      (fs', ts', cs') <- cgStruct fs
      alpha <- UnifVar <$> fresh
      (e', c) <- cg e alpha
      return ((f,e'):fs', (Entry f alpha False):ts', c:cs')


    withSig :: (Expr, Constraint) -> CG (Expr, Constraint)
    withSig (e, c) = pure (Sig e tau, c)

    lookupVar :: VarName -> CG (Type, Constraint)
    lookupVar v = do
      (rho, used, ctx') <- use v <$> get
      put ctx'
      return (rho, if used then Share rho else Sat)

-- | Used for constraint generation for top-level functions.
--   Given a function name, argument name and a function body expression,
--   return an annotated function body along with the constraint that would make
--   it well typed. Also included in the first componenet of the return value
--   are the axioms (constraints placed by the user in the type signature)
--   about polymorphic type variables.
cgFunction :: FunName -> VarName -> Expr -> CG ([Constraint], Expr, Constraint)
cgFunction f x e = do
  alpha <- UnifVar <$> fresh
  beta  <- UnifVar <$> fresh
  let proposedType = Function alpha beta
  modify (push (x,alpha))
  (e', c) <- cg e beta
  used <- topUsed <$> get
  let c' = if used then Sat else Drop alpha
  modify pop
  envs <- ask
  let (c'',axs) = case M.lookup f (types envs) of
                       Nothing -> (Sat, [])
                       Just (Forall vs cs tau) -> (proposedType :< tau, cs)
  pure (axs, e', c :&: c' :&: c'')
