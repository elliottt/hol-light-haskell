module Hol.Equal where

import Error
import Hol.Basics
import Hol.Monad
import Hol.Subst
import Hol.Term

import Control.Monad ((>=>),when,(<=<))
import MonadLib


type Conv = Term -> Hol Theorem

rBETA_CONV :: Conv
rBETA_CONV tm =
  rBETA tm `onError` body `onError` fail "betaConv: Not a beta-redex"
  where
  body = do
    (f,x) <- destApp tm
    v     <- destBoundVar f
    rINST (extendSubst x v emptySubst) =<< rBETA =<< mkApp f v

rAP_TERM :: Term -> Theorem -> Hol Theorem
rAP_TERM tm th = body `onError` fail "apTerm"
  where
  body = do
    eq <- rREFL tm
    rMK_COMB eq th

rAP_THM :: Theorem -> Term -> Hol Theorem
rAP_THM th tm = (rMK_COMB th =<< rREFL tm) `onError` fail "apThm"

rSYM :: Theorem -> Hol Theorem
rSYM th = do
  let tm = seqConcl th
  (l,r) <- destEq tm
  lth   <- rREFL l
  rrtm  <- rator =<< rator tm
  f     <- rAP_TERM rrtm th
  app   <- rMK_COMB f lth
  rEQ_MP app lth

-- | Succeeds when two terms are alpha-convertible.
rALPHA :: Term -> Term -> Hol Theorem
rALPHA tm1 tm2 = body `onError` fail "ALPHA"
  where
  body = do
    tm1' <- rREFL tm1
    tm2' <- rREFL tm2
    rTRANS tm1' tm2'

rALPHA_CONV :: Term -> Term -> Hol Theorem
rALPHA_CONV v tm = rALPHA tm =<< alpha v tm

rGEN_ALPHA_CONV :: Term -> Term -> Hol Theorem
rGEN_ALPHA_CONV v tm
  | isAbs tm  = rALPHA_CONV v tm
  | otherwise = do
    (b,abs) <- destApp tm
    rAP_TERM b =<< rALPHA_CONV v abs

rMK_BINOP :: Term -> Theorem -> Theorem -> Hol Theorem
rMK_BINOP op lth rth = do
  f <- rAP_TERM op lth
  rMK_COMB f rth

rNO_CONV :: Conv
rNO_CONV _ = fail "NO_CONV"

rALL_CONV :: Conv
rALL_CONV  = rREFL

-- | Sequence conversions using transitivity.
rTHENC :: Conv -> Conv -> Conv
rTHENC c1 c2 tm = do
  th1 <- c1 tm
  th2 <- c2 =<< rand (seqConcl th1)
  rTRANS th1 th2

-- | Try the first conversion, falling back on the second conversion if it
-- fails.
rORELSEC :: Conv -> Conv -> Conv
rORELSEC c1 c2 tm = c1 tm `onError` c2 tm

-- | Take the first conversion that succeeds.
rFIRST_CONV :: [Conv] -> Conv
rFIRST_CONV  = foldr rORELSEC rNO_CONV

-- | Apply every conversion, sequentially.
rEVERY_CONV :: [Conv] -> Conv
rEVERY_CONV = foldr rTHENC rALL_CONV

-- | Repeat a conversion until it fails, finishing with ALL_CONV.
rREPEATC :: Conv -> Conv
rREPEATC c = (c `rTHENC` rREPEATC c) `rORELSEC` rALL_CONV

rCHANGED_CONV :: Conv -> Conv
rCHANGED_CONV c tm = do
  th    <- c tm
  (l,r) <- destEq (seqConcl th)
  when (aconv l r) (fail "CHANGED_CONV")
  return th

rTRY_CONV :: Conv -> Conv
rTRY_CONV c = c `rORELSEC` rALL_CONV

rRATOR_CONV :: Conv -> Conv
rRATOR_CONV c tm = do
  (l,r) <- destApp tm
  l'    <- c l
  rAP_THM l' r

rRAND_CONV :: Conv -> Conv
rRAND_CONV c tm = do
  (l,r) <- destApp tm
  rAP_TERM l =<< c r

rLAND_CONV :: Conv -> Conv
rLAND_CONV  = rRATOR_CONV . rRAND_CONV

rCOMB2_CONV :: Conv -> Conv -> Conv
rCOMB2_CONV c1 c2 tm = do
  (l,r) <- destApp tm
  l'    <- c1 l
  r'    <- c2 r
  rMK_COMB l' r'

rCOMB_CONV :: Conv -> Conv
rCOMB_CONV c = rCOMB2_CONV c c

rABS_CONV :: Conv -> Conv
rABS_CONV c tm = do
  (v,bod) <- destAbs tm
  th      <- c bod
  rABS v th `onError` do
    gv    <- genVar =<< typeOf v
    gbod  <- termSubst (extendSubst v gv emptySubst) bod
    gth   <- rABS gv =<< c gbod
    let gtm = seqConcl gth
    (l,r) <- destEq gtm
    v'    <- variant (frees gtm) v
    l' <- alpha v' l
    r' <- alpha v' r
    eq <- rALPHA gtm =<< introEq l' r'
    rEQ_MP eq gth

rBINDER_CONV :: Conv -> Conv
rBINDER_CONV c tm
  | isAbs tm  = rABS_CONV c tm
  | otherwise = rRAND_CONV (rABS_CONV c) tm

rSUB_CONV :: Conv -> Conv
rSUB_CONV c tm
  | isApp tm  = rCOMB_CONV c tm
  | isAbs tm  = rABS_CONV c tm
  | otherwise = rREFL tm

rBINOP_CONV :: Conv -> Conv
rBINOP_CONV c tm = do
  (lop,r) <- destApp tm
  (op,l)  <- destApp lop
  lth <- rAP_TERM op =<< c l
  rMK_COMB lth =<< c r

-- Depth Conversions -----------------------------------------------------------

rONCE_DEPTH_CONV :: Conv -> Conv
rONCE_DEPTH_CONV = rTRY_CONV . rONCE_DEPTH_QCONV

rDEPTH_CONV :: Conv -> Conv
rDEPTH_CONV  = rTRY_CONV . rDEPTH_QCONV

rREDEPTH_CONV :: Conv -> Conv
rREDEPTH_CONV  = rTRY_CONV . rREDEPTH_QCONV

rTOP_DEPTH_CONV :: Conv -> Conv
rTOP_DEPTH_CONV  = rTRY_CONV . rTOP_DEPTH_QCONV

rTOP_SWEEP_CONV :: Conv -> Conv
rTOP_SWEEP_CONV  = rTRY_CONV . rTOP_SWEEP_QCONV

rONCE_DEPTH_QCONV :: Conv -> Conv
rONCE_DEPTH_QCONV c tm = (c `rORELSEC` (rSUB_QCONV (rONCE_DEPTH_QCONV c))) tm

rSUB_QCONV :: Conv -> Conv
rSUB_QCONV c tm
  | isAbs tm  = rABS_CONV c tm
  | otherwise = rCOMB_QCONV c tm

rCOMB_QCONV :: Conv -> Conv
rCOMB_QCONV c tm = do
  (l,r) <- destApp tm
  let lbody = do
        lth <- c l
        rbody lth `onError` rAP_THM lth r
      rbody lth = do
        rth <- c r
        rMK_COMB lth rth
  lbody `onError` (rAP_TERM l =<< c r)

rDEPTH_QCONV :: Conv -> Conv
rDEPTH_QCONV c = rSUB_QCONV (rDEPTH_QCONV c) `rTHENQC` rREPEATQC c

rTHENQC :: Conv -> Conv -> Conv
rTHENQC c1 c2 tm = body1 `onError` c2 tm
  where
  body1 = do
    th1 <- c1 tm
    body2 th1 `onError` return th1
  body2 th1 = do
    th2 <- c2 =<< rand (seqConcl th1)
    rTRANS th1 th2

rTHENCQC :: Conv -> Conv -> Conv
rTHENCQC c1 c2 tm = do
  th1 <- c1 tm
  let body = do
        th2 <- c2 =<< rand (seqConcl th1)
        rTRANS th1 th2
  body `onError` c2 tm

rREPEATQC :: Conv -> Conv
rREPEATQC c = c `rTHENCQC` rREPEATQC c

rREDEPTH_QCONV :: Conv -> Conv
rREDEPTH_QCONV c = rSUB_QCONV (rREDEPTH_QCONV c)
  `rTHENQC` (c `rTHENCQC` rREDEPTH_QCONV c)

rTOP_DEPTH_QCONV :: Conv -> Conv
rTOP_DEPTH_QCONV c =
  rTHENQC (rREPEATQC c)
          (rTHENCQC (rSUB_QCONV (rTOP_DEPTH_QCONV c))
                    (rTHENCQC c (rTOP_DEPTH_QCONV c)))

rTOP_SWEEP_QCONV :: Conv -> Conv
rTOP_SWEEP_QCONV c =
  rTHENQC (rREPEATQC c)
          (rSUB_QCONV (rTOP_SWEEP_QCONV c))


-- Apply at leaves of op-tree --------------------------------------------------

-- XXX: there must be a better way to formulate this.  Using case seems not
-- quite as elegant as it could be.
rDEPTH_BINOP_CONV :: Term -> Conv -> Conv
rDEPTH_BINOP_CONV op c tm =
  case tm of
    App (App op' l) r | op == op' -> do
      (l,r) <- destBinop op tm
      lth   <- rDEPTH_BINOP_CONV op c l
      rth   <- rDEPTH_BINOP_CONV op c r
      l'    <- rAP_TERM op' lth
      rMK_COMB l' rth

    _ -> c tm


rPATH_CONV :: String -> Conv -> Conv
rPATH_CONV s c =
  case s of
    []    -> c
    'l':t -> rRATOR_CONV (rPATH_CONV t c)
    'r':t -> rRAND_CONV  (rPATH_CONV t c)
    _  :t -> rABS_CONV   (rPATH_CONV t c)

rPAT_CONV :: Term -> Conv -> Conv
rPAT_CONV  = fail "rPAT_CONV: not implemented"

-- Conversion To A Rule---------------------------------------------------------

rCONV_RULE :: Conv -> Theorem -> Hol Theorem
rCONV_RULE c th = do
  th' <- c (seqConcl th)
  rEQ_MP th' th

rBETA_RULE :: Theorem -> Hol Theorem
rBETA_RULE  = rCONV_RULE (rREDEPTH_CONV rBETA_CONV)
