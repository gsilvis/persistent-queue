{-# LANGUAGE GADTs, KindSignatures #-}

data Zero
data Succ n

data NLayered n :: (* -> *) -> (* -> *) where
  L0 :: a -> NLayered Zero f a
  LN :: f (NLayered n f a) -> NLayered (Succ n) f a

data Pair a = Pair a a

data R0Exposed
data R2Exposed
data L0Exposed
data L2Exposed

data LHU a :: * -> * where
  LH1 :: NLayered n Pair a -> LHU a n

data LHM a :: * -> * -> * -> * where
  LH0 :: () ->
         LHM a n L2Exposed L0Exposed
  LH2 :: Pair (NLayered n Pair a) ->
         LHM a n L0Exposed L2Exposed

data RHU a :: * -> * where
  RH1 :: NLayered n Pair a -> RHU a n

data RHM a :: * -> * -> * -> * where
  RH0 :: () ->
         RHM a n R2Exposed R0Exposed
  RH2 :: Pair (NLayered n Pair a) ->
         RHM a n R0Exposed R2Exposed

data L1 a :: * -> * -> * where
  L1E :: L1 a bottom bottom
  L1L :: (LHU a top, RHU a top) ->
         L1 a (Succ top) bottom ->
         L1 a top bottom

data L2L a :: * -> * -> * -> * -> * where
  L2LE :: L2L a bottom bottom lexp lexp
  L2LL :: (LHM a top lmid lexp, RHU a top) ->
          L1 a (Succ top) mid ->
          L2L a mid bottom lreq lmid ->
          L2L a top bottom lreq lexp

data L2R a :: * -> * -> * -> * -> * where
  L2RE :: L2R a bottom bottom rexp rexp
  L2RL :: (LHU a top, RHM a top rmid rexp) ->
          L1 a (Succ top) mid ->
          L2R a mid bottom rreq rmid ->
          L2R a top bottom rreq rexp

data L3L a :: * -> * -> * -> * -> * -> * -> * where
  L3LE :: L3L a bottom bottom lexp lexp rexp rexp
  L3LL :: (LHM a top lm2 lexp, RHU a top) ->
          L1 a (Succ top) mtop ->
          L2L a mtop mbot lm1 lm2 ->
          L3R a mbot bot lreq lm1 rreq rexp ->
          L3L a top bot lreq lexp rreq rexp

data L3R a :: * -> * -> * -> * -> * -> * -> * where
  L3RE :: L3R a bottom bottom lexp lexp rexp rexp
  L3RL :: (LHU a top, RHM a top rm2 rexp) ->
          L1 a (Succ top) mtop ->
          L2R a mtop mbot rm1 rm2 ->
          L3L a mbot bot lreq lexp rreq rm1 ->
          L3R a top bot lreq lexp rreq rexp

data L3 a :: * -> * -> * -> * -> * -> * -> * where
  L3E :: L3 a bottom bottom lexp lexp rexp rexp
  L3L :: (LHM a top lm2 lexp, RHU a top) ->
         L1 a (Succ top) mtop ->
         L2L a mtop mbot lm1 lm2 ->
         L3R a mbot bot lreq lm1 rreq rexp ->
         L3 a top bot lreq lexp rreq rexp
  L3R :: (LHU a top, RHM a top rm2 rexp) ->
         L1 a (Succ top) mtop ->
         L2R a mtop mbot rm1 rm2 ->
         L3L a mbot bot lreq lexp rreq rm1 ->
         L3 a top bot lreq lexp rreq rexp

data Final c = Final1 c
             | Final2 c c
             | Final3 c c c
             | Final4 c c c c
             | Final5 c c c c c

data L4 a :: * -> * -> * -> * where
  L4E :: Final (NLayered top Pair a) ->
         L4 a top lexposure rexposure
  L4 :: (LHM a top lmid lexp, RHM a top rmid rexp) ->
        S4 a (Succ top) lmid rmid ->
        L4 a top lexp rexp

data S4 a :: * -> * -> * -> * where
  S4 :: L1 a top mid ->
        L3 a mid bot lbot ltop rbot rtop ->
        L4 a bot lbot rbot ->
        S4 a top ltop rtop

data Queue a = Q0 | QN (S4 a Zero L0Exposed R0Exposed)

empty :: Queue a
empty = Q0

singleton :: a -> Queue a
singleton a = QN (S4 L1E L3E (L4E (Final1 (L0 a))))

doubleton :: a -> Queue a
doubleton a = QN (S4 L1E L3E (L4E (Final2 (L0 a) (L0 a))))


bestowL :: L1 a top mid ->
           (LHM a mid lreq lexp, RHU a mid) ->
           S4 a (Succ mid) lreq rexp ->
           S4 a top lexp rexp
bestowL ones level (S4 l1 l3 l4) = S4 ones result l4 where
  result = case l3 of
    L3L under m1 m2 m3 -> L3L level l1 (L2LL under m1 m2) m3
    L3R under m1 m2 m3 -> L3L level l1 L2LE (L3RL under m1 m2 m3)
    L3E -> L3L level l1 L2LE L3RE

bestowR :: L1 a top mid ->
           (LHU a mid, RHM a mid rreq rexp) ->
           S4 a (Succ mid) lexp rreq ->
           S4 a top lexp rexp
bestowR ones level (S4 l1 l3 l4) = S4 ones result l4 where
  result = case l3 of
    L3R under m1 m2 m3 -> L3R level l1 (L2RL under m1 m2) m3
    L3L under m1 m2 m3 -> L3R level l1 L2RE (L3LL under m1 m2 m3)
    L3E -> L3R level l1 L2RE L3LE

pushUU :: (LHU a n, RHU a n) ->
          S4 a (Succ n) lexp rexp ->
          S4 a n lexp rexp
pushUU level (S4 l1 l3 l4) = S4 (L1L level l1) l3 l4

pushUM :: (LHU a n, RHM a n rreq rexp) ->
          S4 a (Succ n) lexp rreq ->
          S4 a n lexp rexp
pushUM level body = bestowR L1E level body

pushMU :: (LHM a n lreq lexp, RHU a n) ->
          S4 a (Succ n) lreq rexp ->
          S4 a n lexp rexp
pushMU level body = bestowL L1E level body

pushMM :: (LHM a n lreq lexp, RHM a n rreq rexp) ->
          S4 a (Succ n) lreq rreq ->
          S4 a n lexp rexp
pushMM level body = S4 L1E L3E (L4 level body)

push2l :: L1 a n1 n2 ->
          L2L a n2 n3 lmid lexp ->
          L3R a n3 n4 lreq lmid rreq rexp ->
          L4 a n4 lreq rreq ->
          S4 a n1 lexp rexp
push2l l1 (L2LE) (L3RE) l4 = S4 l1 L3E l4
push2l l1 (L2LE) (L3RL lev m1 m2 m3) l4 = S4 l1 (L3R lev m1 m2 m3) l4
push2l l1 (L2LL level m1 m2) l3 l4 = S4 l1 (L3L level m1 m2 l3) l4

push2r :: L1 a n1 n2 ->
          L2R a n2 n3 rmid rexp ->
          L3L a n3 n4 lreq lexp rreq rmid ->
          L4 a n4 lreq rreq ->
          S4 a n1 lexp rexp
push2r l1 (L2RE) (L3LE) l4 = S4 l1 L3E l4
push2r l1 (L2RE) (L3LL lev m1 m2 m3) l4 = S4 l1 (L3L lev m1 m2 m3) l4
push2r l1 (L2RL level m1 m2) l3 l4 = S4 l1 (L3R level m1 m2 l3) l4

bestow2L :: L1 a n1 n2 ->
            L2R a n2 n3 rreq rexp ->
            (LHM a n3 lreq lexp, RHU a n3) ->
            S4 a (Succ n3) lreq rreq ->
            S4 a n1 lexp rexp
bestow2L ones twos level (S4 l1 l3 l4) = case twos of
  L2RE -> bestowL ones level (S4 l1 l3 l4)
  L2RL upper m1 m2 -> S4 ones (L3R upper m1 m2 result) l4 where
    result = case l3 of
      L3E -> L3LL level l1 L2LE L3RE
      L3R lower n1 n2 n3 -> L3LL level l1 L2LE (L3RL lower n1 n2 n3)
      L3L lower n1 n2 n3 -> L3LL level l1 (L2LL lower n1 n2) n3

bestow2R :: L1 a n1 n2 ->
            L2L a n2 n3 lreq lexp ->
            (LHU a n3, RHM a n3 rreq rexp) ->
            S4 a (Succ n3) lreq rreq ->
            S4 a n1 lexp rexp
bestow2R ones twos level (S4 l1 l3 l4) = case twos of
  L2LE -> bestowR ones level (S4 l1 l3 l4)
  L2LL upper m1 m2 -> S4 ones (L3L upper m1 m2 result) l4 where
    result = case l3 of
      L3E -> L3RL level l1 L2RE L3LE
      L3L lower n1 n2 n3 -> L3RL level l1 L2RE (L3LL lower n1 n2 n3)
      L3R lower n1 n2 n3 -> L3RL level l1 (L2RL lower n1 n2) n3


npushl :: NLayered n Pair a ->
           S4 a n L0Exposed rexposure ->
           S4 a n L2Exposed rexposure
npushl a (S4 l1 l3 l4) = case l1 of
  L1L (LH1 l, RH1 r) m1 ->
    pushMU (LH2 (Pair a l), RH1 r) (S4 m1 l3 l4)
  L1E -> case l3 of
    L3L (LH0 (), RH1 r) m1 m2 m3 ->
      pushUU (LH1 a, RH1 r) $
      push2l m1 m2 m3 l4
    L3R (LH1 l, r) m1 m2 m3 ->
      pushMM (LH2 (Pair a l), r) $
      push2r m1 m2 m3 l4
    L3E -> case l4 of
      L4 (LH0 (), r) rest -> pushUM (LH1 a, r) rest
      L4E (Final1 b) ->       S4 L1E L3E (L4E (Final2 a b))
      L4E (Final2 b c) ->     S4 L1E L3E (L4E (Final3 a b c))
      L4E (Final3 b c d) ->   S4 L1E L3E (L4E (Final4 a b c d))
      L4E (Final4 b c d e) -> S4 L1E L3E (L4E (Final5 a b c d e))
      L4E (Final5 p q r s b) -> S4 (L1L (LH1 a, RH1 b) L1E)
        L3E (L4E (Final2 (LN (Pair p q)) (LN (Pair r s))))


fix2l :: S4 a n L2Exposed rexposure ->
         S4 a n L0Exposed rexposure
fix2l (S4 l1 l3 l4) = case l3 of
  L3L (LH2 l, RH1 r) m1 m2 m3 ->
    bestowL l1 (LH0 (), RH1 r) $
    npushl (LN l) $
    push2l m1 m2 m3 l4
  L3R level m1 m2 m3 ->
    bestowR l1 level $ case m3 of
    L3LL (LH2 l, RH1 r) n1 n2 n3 ->
      bestow2L m1 m2 (LH0 (), RH1 r) $
      npushl (LN l) $
      push2l n1 n2 n3 l4
    L3LE -> push2r m1 m2 L3LE $ case l4 of
      L4 (LH2 l, r) rest ->
        L4 (LH0 (), r) (npushl (LN l) rest)
      L4E final -> L4E final
  L3E -> S4 l1 L3E $ case l4 of
    L4 (LH2 l, r) rest ->
      L4 (LH0 (), r) (npushl (LN l) rest)
    L4E final -> L4E final


pushl :: a -> Queue a -> Queue a
pushl a Q0 = QN (S4 L1E L3E (L4E (Final1 (L0 a))))
pushl a (QN q) = QN (fix2l (npushl (L0 a) q))

npopl :: S4 a n L2Exposed rexposure ->
         (NLayered n Pair a, Maybe (S4 a n L0Exposed rexposure))
npopl (S4 l1 l3 l4) = case l1 of
  L1L (LH1 a, RH1 r) m1 -> (a, Just rest) where
    rest = pushMU (LH0 (), RH1 r) (S4 m1 l3 l4)
  L1E -> case l3 of
    L3L (LH2 (Pair a l), RH1 r) m1 m2 m3 -> (a, Just rest) where
      rest = pushUU (LH1 l, RH1 r) $
             push2l m1 m2 m3 l4
    L3R (LH1 a, r) m1 m2 m3 -> (a, Just rest) where
      rest = pushMM (LH0 (), r) $
             push2r m1 m2 m3 l4
    L3E -> case l4 of
      L4 (LH2 (Pair a l), r) inner -> (a, Just rest) where
        rest = pushUM (LH1 l, r) inner
      L4E (Final5 a b c d e) -> (a, Just (S4 L1E L3E (L4E (Final4 b c d e))))
      L4E (Final4 a b c d) ->   (a, Just (S4 L1E L3E (L4E (Final3 b c d))))
      L4E (Final3 a b c) ->     (a, Just (S4 L1E L3E (L4E (Final2 b c))))
      L4E (Final2 a b) ->       (a, Just (S4 L1E L3E (L4E (Final1 b))))
      L4E (Final1 a) -> (a, Nothing)



fix0l :: S4 a n L0Exposed rexposure ->
         S4 a n L2Exposed rexposure
fix0l (S4 l1 l3 l4) = case l3 of
  L3L (LH0 (), RH1 r) m1 m2 m3 ->
    case npopl (push2l m1 m2 m3 l4) of
      (LN l, Just result) -> bestowL l1 (LH2 l, RH1 r) result
      (LN (Pair a b), Nothing) -> S4 l1 L3E (L4E (Final3 a b r))
  L3R level m1 m2 m3 ->
    bestowR l1 level $ case m3 of
    L3LL (LH0 (), RH1 r) n1 n2 n3 ->
      case npopl (push2l n1 n2 n3 l4) of
        (LN l, Just result) ->
          bestow2L m1 m2 (LH2 l, RH1 r) result
        (LN (Pair a b), Nothing) ->
          push2r m1 m2 L3LE (L4E (Final3 a b r))
    L3LE -> push2r m1 m2 L3LE $ case l4 of
      L4 (LH0 (), r) rest -> case npopl rest of
          (LN l, Just new) -> L4 (LH2 l, r) new
          (LN (Pair a b), Nothing) -> case r of
            RH0 () -> L4E (Final2 a b)
            RH2 (Pair q r) -> L4E (Final4 a b q r)
      L4E final -> L4E final
  L3E -> S4 l1 L3E $ case l4 of
    L4 (LH0 (), r) rest -> case npopl rest of
      (LN l, Just new) -> L4 (LH2 l, r) new
      (LN (Pair a b), Nothing) -> case r of
        RH0 () -> L4E (Final2 a b)
        RH2 (Pair q r) -> L4E (Final4 a b q r)
    L4E final -> L4E final


popl :: Queue a -> Maybe (a, Queue a)
popl Q0 = Nothing
popl (QN q) = case npopl (fix0l q) of
  (L0 a, Nothing) -> Just (a, Q0)
  (L0 a, Just q) -> Just (a, QN q)


npushr :: NLayered n Pair a ->
           S4 a n lexposure R0Exposed ->
           S4 a n lexposure R2Exposed
npushr a (S4 l1 l3 l4) = case l1 of
  L1L (LH1 l, RH1 r) m1 ->
    pushUM (LH1 l, RH2 (Pair r a)) (S4 m1 l3 l4)
  L1E -> case l3 of
    L3R (LH1 l, RH0 ()) m1 m2 m3 ->
      pushUU (LH1 l, RH1 a) $
      push2r m1 m2 m3 l4
    L3L (l, RH1 r) m1 m2 m3 ->
      pushMM (l, RH2 (Pair r a)) $
      push2l m1 m2 m3 l4
    L3E -> case l4 of
      L4 (l, RH0 ()) rest -> pushMU (l, RH1 a) rest
      L4E (Final1 b) ->       S4 L1E L3E (L4E (Final2 b a))
      L4E (Final2 b c) ->     S4 L1E L3E (L4E (Final3 b c a))
      L4E (Final3 b c d) ->   S4 L1E L3E (L4E (Final4 b c d a))
      L4E (Final4 b c d e) -> S4 L1E L3E (L4E (Final5 b c d e a))
      L4E (Final5 b p q r s) -> S4 (L1L (LH1 b, RH1 a) L1E)
        L3E (L4E (Final2 (LN (Pair p q)) (LN (Pair r s))))


fix2r :: S4 a n lexposure R2Exposed ->
         S4 a n lexposure R0Exposed
fix2r (S4 l1 l3 l4) = case l3 of
  L3R (LH1 l, RH2 r) m1 m2 m3 ->
    bestowR l1 (LH1 l, RH0 ()) $
    npushr (LN r) $
    push2r m1 m2 m3 l4
  L3L level m1 m2 m3 -> bestowL l1 level $ case m3 of
    L3RL (LH1 l, RH2 r) n1 n2 n3 ->
      bestow2R m1 m2 (LH1 l, RH0 ()) $
      npushr (LN r) $
      push2r n1 n2 n3 l4
    L3RE -> push2l m1 m2 L3RE $ case l4 of
      L4 (l, RH2 r) rest ->
        L4 (l, RH0 ()) (npushr (LN r) rest)
      L4E final -> L4E final
  L3E -> S4 l1 L3E $ case l4 of
    L4 (l, RH2 r) rest ->
      L4 (l, RH0 ()) (npushr (LN r) rest)
    L4E final -> L4E final

pushr :: a -> Queue a -> Queue a
pushr a Q0 = QN (S4 L1E L3E (L4E (Final1 (L0 a))))
pushr a (QN q) = QN (fix2r (npushr (L0 a) q))


npopr :: S4 a n lexposure R2Exposed ->
         (NLayered n Pair a, Maybe (S4 a n lexposure R0Exposed))
npopr (S4 l1 l3 l4) = case l1 of
  L1L (LH1 l, RH1 a) m1 -> (a, Just rest) where
    rest = pushUM (LH1 l, RH0 ()) (S4 m1 l3 l4)
  L1E -> case l3 of
    L3R (LH1 l, RH2 (Pair r a)) m1 m2 m3 -> (a, Just rest) where
      rest = pushUU (LH1 l, RH1 r) $
             push2r m1 m2 m3 l4
    L3L (l, RH1 a) m1 m2 m3 -> (a, Just rest) where
      rest = pushMM (l, RH0 ()) $
             push2l m1 m2 m3 l4
    L3E -> case l4 of
      L4 (l, RH2 (Pair r a)) inner -> (a, Just rest) where
        rest = pushMU (l, RH1 r) inner
      L4E (Final5 v w x y z) -> (z, Just (S4 L1E L3E (L4E (Final4 v w x y))))
      L4E (Final4   w x y z) -> (z, Just (S4 L1E L3E (L4E (Final3   w x y))))
      L4E (Final3     x y z) -> (z, Just (S4 L1E L3E (L4E (Final2     x y))))
      L4E (Final2       y z) -> (z, Just (S4 L1E L3E (L4E (Final1       y))))
      L4E (Final1         z) -> (z, Nothing)


fix0r :: S4 a n lexposure R0Exposed ->
         S4 a n lexposure R2Exposed
fix0r (S4 l1 l3 l4) = case l3 of
  L3R (LH1 l, RH0 ()) m1 m2 m3 ->
    case npopr (push2r m1 m2 m3 l4) of
      (LN r, Just result) -> bestowR l1 (LH1 l, RH2 r) result
      (LN (Pair a b), Nothing) -> S4 l1 L3E (L4E (Final3 l a b))
  L3L level m1 m2 m3 -> bestowL l1 level $ case m3 of
    L3RL (LH1 l, RH0 ()) n1 n2 n3 ->
      case npopr (push2r n1 n2 n3 l4) of
        (LN r, Just result) ->
          bestow2R m1 m2 (LH1 l, RH2 r) result
        (LN (Pair a b), Nothing) ->
          push2l m1 m2 L3RE (L4E (Final3 l a b))
    L3RE -> push2l m1 m2 L3RE $ case l4 of
      L4 (l, RH0 ()) rest -> case npopr rest of
          (LN r, Just new) -> L4 (l, RH2 r) new
          (LN (Pair a b), Nothing) -> case l of
            LH0 () -> L4E (Final2 a b)
            LH2 (Pair q r) -> L4E (Final4 q r a b)
      L4E final -> L4E final
  L3E -> S4 l1 L3E $ case l4 of
    L4 (l, RH0 ()) rest -> case npopr rest of
      (LN r, Just new) -> L4 (l, RH2 r) new
      (LN (Pair a b), Nothing) -> case l of
        LH0 () -> L4E (Final2 a b)
        LH2 (Pair q r) -> L4E (Final4 q r a b)
    L4E final -> L4E final


popr :: Queue a -> Maybe (a, Queue a)
popr Q0 = Nothing
popr (QN q) = case npopr (fix0r q) of
  (L0 a, Nothing) -> Just (a, Q0)
  (L0 a, Just q) -> Just (a, QN q)
