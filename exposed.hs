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

data LModifying
data LUnmodifying
data RModifying
data RUnmodifying

data Leftist
data Rightist

data LHalf a :: * -> * -> * -> * -> * where
  LH0 :: () ->
         LHalf a n LModifying L2Exposed L0Exposed
  LH1 :: NLayered n Pair a ->
         LHalf a n LUnmodifying lexposure lexposure
  LH2 :: Pair (NLayered n Pair a) ->
         LHalf a n LModifying L0Exposed L2Exposed

data RHalf a :: * -> * -> * -> * -> * where
  RH0 :: () ->
         RHalf a n RModifying R2Exposed R0Exposed
  RH1 :: NLayered n Pair a ->
         RHalf a n RUnmodifying rexposure rexposure
  RH2 :: Pair (NLayered n Pair a) ->
         RHalf a n RModifying R0Exposed R2Exposed

data Level a :: * -> * -> * -> * -> * -> * -> * -> * where
  Level :: LHalf a n lmod lreq lexp ->
           RHalf a n rmod rreq rexp ->
           Level a n lmod lreq lexp rmod rreq rexp

data Level' a :: * -> * -> * -> * -> * -> * where
  LevelUU :: Level a n LUnmodifying lexp lexp RUnmodifying rexp rexp ->
             Level' a n lexp lexp rexp rexp
  LevelUM :: Level a n LUnmodifying lexp lexp RModifying rreq rexp ->
             Level' a n lexp lexp rreq rexp
  LevelMU :: Level a n LModifying lreq lexp RUnmodifying rexp rexp ->
             Level' a n lreq lexp rexp rexp
  LevelMM :: Level a n LModifying lreq lexp RModifying rreq rexp ->
             Level' a n lreq lexp rreq rexp
  
data L1 a :: * -> * -> * where
  L1E :: L1 a bottom bottom
  L1L :: Level a top LUnmodifying lexp lexp RUnmodifying rexp rexp ->
         L1 a (Succ top) bottom ->
         L1 a top bottom

data L2L a :: * -> * -> * -> * -> * where
  L2LE :: L2L a bottom bottom lexp lexp
  L2LL :: Level a top LModifying lmid lexp RUnmodifying rexp rexp ->
          L1 a (Succ top) mid ->
          L2L a mid bottom lreq lmid ->
          L2L a top bottom lreq lexp

data L2R a :: * -> * -> * -> * -> * where
  L2RE :: L2R a bottom bottom rexp rexp
  L2RL :: Level a top LUnmodifying lexp lexp RModifying rmid rexp ->
          L1 a (Succ top) mid ->
          L2R a mid bottom rreq rmid ->
          L2R a top bottom rreq rexp

data L3 a :: * -> * -> * -> * -> * -> * -> * -> * where
  L3E :: L3 a bottom bottom lexp lexp rexp rexp politics
  L3L :: Level a top LModifying lm2 lexp RUnmodifying rexp rexp ->
         L1 a (Succ top) mtop ->
         L2L a mtop mbot lm1 lm2 ->
         L3 a mbot bot lreq lm1 rreq rexp Rightist ->
         L3 a top bot lreq lexp rreq rexp Leftist
  L3R :: Level a top LUnmodifying lexp lexp RModifying rm2 rexp ->
         L1 a (Succ top) mtop ->
         L2R a mtop mbot rm1 rm2 ->
         L3 a mbot bot lreq lexp rreq rm1 Leftist ->
         L3 a top bot lreq lexp rreq rexp Rightist

data Final c = Final1 c
             | Final2 c c
             | Final3 c c c
             | Final4 c c c c
             | Final5 c c c c c

data L4 a :: * -> * -> * -> * where
  L4E :: Final (NLayered top Pair a) ->
         L4 a top lexposure rexposure
  L4 :: Level a top LModifying lmid lexp RModifying rmid rexp ->
        S4 a (Succ top) lmid rmid ->
        L4 a top lexp rexp

data S4 a :: * -> * -> * -> * where
  S4 :: L1 a top mid ->
        L3 a mid bot lbot ltop rbot rtop politics ->
        L4 a bot lbot rbot ->
        S4 a top ltop rtop

data Queue' a :: * -> * -> * -> * where
  Q0 :: Queue' a n lexposure rexposure
  QN :: S4 a n lexposure rexposure ->
        Queue' a n lexposure rexposure

data Queue a = Q00 (Queue' a Zero L0Exposed R0Exposed)
             | Q02 (Queue' a Zero L0Exposed R2Exposed)
             | Q20 (Queue' a Zero L2Exposed R0Exposed)
             | Q22 (Queue' a Zero L2Exposed R2Exposed)

empty :: Queue a
empty = Q00 Q0

singleton :: a -> Queue a
singleton a = Q00 (QN (S4 L1E L3E (L4E (Final1 (L0 a)))))

doubleton :: a -> Queue a
doubleton a = Q00 (QN (S4 L1E L3E (L4E (Final2 (L0 a) (L0 a)))))


bestowL :: L1 a top mid ->
           Level a mid LModifying lreq lexp RUnmodifying rexp rexp ->
           S4 a (Succ mid) lreq rexp ->
           S4 a top lexp rexp
bestowL ones level (S4 l1 l3 l4) = case l3 of
  L3L under m1 m2 m3 -> S4 ones (L3L level l1 (L2LL under m1 m2) m3) l4
  m3@(L3R _ _ _ _) -> S4 ones (L3L level l1 L2LE m3) l4
  L3E -> S4 ones (L3L level l1 L2LE L3E) l4


bestowR :: L1 a top mid ->
           Level a mid LUnmodifying lexp lexp RModifying rreq rexp ->
           S4 a (Succ mid) lexp rreq ->
           S4 a top lexp rexp
bestowR ones level (S4 l1 l3 l4) = case l3 of
  L3R under m1 m2 m3 -> S4 ones (L3R level l1 (L2RL under m1 m2) m3) l4
  m3@(L3L _ _ _ _) -> S4 ones (L3R level l1 L2RE m3) l4
  L3E -> S4 ones (L3R level l1 L2RE L3E) l4


pushlevel :: Level' a n lreq lexp rreq rexp ->
             S4 a (Succ n) lreq rreq ->
             S4 a n lexp rexp
pushlevel (LevelUU level) (S4 l1 l3 l4) = S4 (L1L level l1) l3 l4
pushlevel (LevelUM level) body = bestowR L1E level body
pushlevel (LevelMU level) body = bestowL L1E level body
pushlevel (LevelMM (Level l r)) body = S4 L1E L3E (L4 (Level l r) body)


npushl' :: NLayered n Pair a ->
           S4 a n L0Exposed rexposure ->
           S4 a n L2Exposed rexposure
npushl' a (S4 l1 l3 l4) = case l1 of
  L1L (Level (LH1 l) (RH1 r)) m1 ->
    pushlevel (LevelMU (Level (LH2 (Pair a l)) (RH1 r))) (S4 m1 l3 l4)
  L1E -> case l3 of
    L3L (Level (LH0 ()) (RH1 r)) m1 m2 m3 ->
      pushlevel (LevelUU (Level (LH1 a) (RH1 r))) $ case m2 of
        L2LE -> (S4 m1 m3 l4)
        L2LL (Level kl (RH1 kr)) n1 n2 -> 
          S4 m1 (L3L (Level kl (RH1 kr)) n1 n2 m3) l4
    L3R (Level (LH1 l) r) m1 m2 m3 ->
      pushlevel (LevelMM (Level (LH2 (Pair a l)) r)) $ case m2 of
        L2RE -> S4 m1 m3 l4
        L2RL (Level (LH1 kl) kr) n1 n2 ->
          S4 m1 (L3R (Level (LH1 kl) kr) n1 n2 m3) l4
    L3E -> case l4 of
      L4 (Level (LH0 ()) r) rest ->
        pushlevel (LevelUM (Level (LH1 a) r)) rest
      L4E (Final1 b) ->       S4 L1E L3E (L4E (Final2 a b))
      L4E (Final2 b c) ->     S4 L1E L3E (L4E (Final3 a b c))
      L4E (Final3 b c d) ->   S4 L1E L3E (L4E (Final4 a b c d))
      L4E (Final4 b c d e) -> S4 L1E L3E (L4E (Final5 a b c d e))
      L4E (Final5 p q r s b) -> S4 (L1L (Level (LH1 a) (RH1 b)) L1E)
        L3E (L4E (Final2 (LN (Pair p q)) (LN (Pair r s))))

npushl :: NLayered n Pair a ->
          Queue' a n L0Exposed rexposure ->
          Queue' a n L2Exposed rexposure
npushl a Q0 = QN (S4 L1E L3E (L4E (Final1 a)))
npushl a (QN q) = QN (npushl' a q)

fix2l :: Queue' a n L2Exposed rexposure ->
         Queue' a n L0Exposed rexposure
fix2l Q0 = Q0
fix2l (QN (S4 l1 l3 l4)) = QN $ case l3 of
  L3L (Level (LH2 l) (RH1 r)) m1 m2 m3 ->
    bestowL l1 (Level (LH0 ()) (RH1 r)) $ npushl' (LN l) $ case m2 of
      L2LE -> (S4 m1 m3 l4)
      L2LL (Level kl (RH1 kr)) n1 n2 -> 
        S4 m1 (L3L (Level kl (RH1 kr)) n1 n2 m3) l4
  L3R (Level (LH1 kl) kr) m1 m2 m3 -> case m3 of
    L3L (Level (LH2 l) (RH1 r)) n1 n2 n3 -> case n2 of
      L2LL (Level (LH0 ()) (RH1 ir)) o1 o2 ->
        case npushl' (LN l) (S4 n1 (L3L (Level (LH0 ()) (RH1 ir)) o1 o2 n3) l4) of
        S4 p1 p3 p4 -> S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 result) p4 where
          result = case p3 of
            L3E -> L3L (Level (LH0 ()) (RH1 r)) p1 L2LE L3E
            q3@(L3R _ _ _ _) -> L3L (Level (LH0 ()) (RH1 r)) p1 L2LE q3
            (L3L inner q1 q2 q3) ->
              L3L (Level (LH0 ()) (RH1 r)) p1 (L2LL inner q1 q2) q3
      L2LE -> case npushl' (LN l) (S4 n1 n3 l4) of
        S4 o1 o3 o4 -> S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 result) o4 where
          result = case o3 of
            L3E -> (L3L (Level (LH0 ()) (RH1 r)) o1 L2LE L3E)
            p3@(L3R _ _ _ _) -> (L3L (Level (LH0 ()) (RH1 r)) o1 L2LE p3)
            L3L inner p1 p2 p3 ->
              (L3L (Level (LH0 ()) (RH1 r)) o1 (L2LL inner p1 p2) p3)
    L3E -> S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 L3E) $ case l4 of
      L4 (Level (LH2 l) r) rest ->
        L4 (Level (LH0 ()) r) (npushl' (LN l) rest)
      L4E final -> L4E final
  L3E -> S4 l1 L3E $ case l4 of
    L4 (Level (LH2 l) r) rest ->
      L4 (Level (LH0 ()) r) (npushl' (LN l) rest)
    L4E final -> L4E final


pushl :: a -> Queue a -> Queue a
pushl a (Q00 q) = Q20 (npushl (L0 a) q)
pushl a (Q02 q) = Q22 (npushl (L0 a) q)
pushl a (Q20 q) = Q20 (npushl (L0 a) (fix2l q))
pushl a (Q22 q) = Q22 (npushl (L0 a) (fix2l q))


npopl :: S4 a n L2Exposed rexposure ->
         (NLayered n Pair a, Queue' a n L0Exposed rexposure)
npopl (S4 l1 l3 l4) = case l1 of
  L1L (Level (LH1 a) (RH1 r)) m1 -> (a, QN rest) where
    rest = pushlevel (LevelMU (Level (LH0 ()) (RH1 r))) (S4 m1 l3 l4)
  L1E -> case l3 of
    L3L (Level (LH2 (Pair a l)) (RH1 r)) m1 m2 m3 -> (a, QN rest) where
      rest = pushlevel (LevelUU (Level (LH1 l) (RH1 r))) $ case m2 of
        L2LE -> S4 m1 m3 l4
        L2LL (Level kl (RH1 kr)) n1 n2 ->
          S4 m1 (L3L (Level kl (RH1 kr)) n1 n2 m3) l4
    L3R (Level (LH1 a) r) m1 m2 m3 -> (a, QN rest) where
      rest = pushlevel (LevelMM (Level (LH0 ()) r)) $ case m2 of
        L2RE -> S4 m1 m3 l4
        L2RL (Level (LH1 kl) kr) n1 n2 ->
          S4 m1 (L3R (Level (LH1 kl) kr) n1 n2 m3) l4
    L3E -> case l4 of
      L4 (Level (LH2 (Pair a l)) r) inner -> (a, QN rest) where
        rest = pushlevel (LevelUM (Level (LH1 l) r)) inner
      L4E (Final5 a b c d e) -> (a, QN (S4 L1E L3E (L4E (Final4 b c d e))))
      L4E (Final4 a b c d) ->   (a, QN (S4 L1E L3E (L4E (Final3 b c d))))
      L4E (Final3 a b c) ->     (a, QN (S4 L1E L3E (L4E (Final2 b c))))
      L4E (Final2 a b) ->       (a, QN (S4 L1E L3E (L4E (Final1 b))))
      L4E (Final1 a) -> (a, Q0)

fix0l :: Queue' a n L0Exposed rexposure ->
         Queue' a n L2Exposed rexposure
fix0l Q0 = Q0
fix0l (QN (S4 l1 l3 l4)) = QN $ case l3 of
  L3L (Level (LH0 ()) (RH1 r)) m1 m2 m3 ->
    case npopl poppee of
      (LN l, QN result) -> bestowL l1 (Level (LH2 l) (RH1 r)) result
      (LN (Pair a b), Q0) -> S4 l1 L3E (L4E (Final3 a b r))
    where
      poppee = case m2 of
        L2LE -> S4 m1 m3 l4
        L2LL (Level kl (RH1 kr)) n1 n2 ->
          S4 m1 (L3L (Level kl (RH1 kr)) n1 n2 m3) l4
  L3R (Level (LH1 kl) kr) m1 m2 m3 -> case m3 of
    L3L (Level (LH0 ()) (RH1 r)) n1 n2 n3 -> case n2 of
      L2LL (Level (LH2 l) (RH1 ir)) o1 o2 ->
        case npopl (S4 n1 (L3L (Level (LH2 l) (RH1 ir)) o1 o2 n3) l4) of
          (LN l, QN (S4 p1 p3 p4)) ->
            S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 result) p4 where
              result = case p3 of
                L3E -> L3L (Level (LH2 l) (RH1 r)) p1 L2LE L3E
                q3@(L3R _ _ _ _) -> L3L (Level (LH2 l) (RH1 r)) p1 L2LE q3
                L3L inner q1 q2 q3 ->
                  L3L (Level (LH2 l) (RH1 r)) p1 (L2LL inner q1 q2) q3
          (LN (Pair a b), Q0) ->
            S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 L3E) (L4E (Final3 a b r))
      L2LE -> case npopl (S4 n1 n3 l4) of
        (LN l, QN (S4 o1 o3 o4)) ->
          S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 result) o4 where
            result = case o3 of
              L3E -> L3L (Level (LH2 l) (RH1 r)) o1 L2LE L3E
              p3@(L3R _ _ _ _) -> L3L (Level (LH2 l) (RH1 r)) o1 L2LE p3
              L3L inner p1 p2 p3 ->
                L3L (Level (LH2 l) (RH1 r)) o1 (L2LL inner p1 p2) p3
        (LN (Pair a b), Q0) ->
          S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 L3E) (L4E (Final3 a b r))
    L3E -> S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 L3E) $ case l4 of
      L4 (Level (LH0 ()) r) rest -> case npopl rest of
          (LN l, QN new) -> L4 (Level (LH2 l) r) new
          (LN (Pair a b), Q0) -> case r of
            RH0 () -> L4E (Final2 a b)
            RH2 (Pair q r) -> L4E (Final4 a b q r)
      L4E final -> L4E final
  L3E -> S4 l1 L3E $ case l4 of
    L4 (Level (LH0 ()) r) rest -> case npopl rest of
      (LN l, QN new) -> L4 (Level (LH2 l) r) new
      (LN (Pair a b), Q0) -> case r of
        RH0 () -> L4E (Final2 a b)
        RH2 (Pair q r) -> L4E (Final4 a b q r)
    L4E final -> L4E final


popl :: Queue a -> Maybe (a, Queue a)
popl (Q00 q) = popl (Q20 (fix0l q))
popl (Q02 q) = popl (Q22 (fix0l q))
popl (Q20 (QN q)) = Just $ case npopl q of
  (L0 a, new) -> (a, Q00 new)
popl (Q22 (QN q)) = Just $ case npopl q of
  (L0 a, new) -> (a, Q02 new)
popl (Q20 Q0) = Nothing
popl (Q22 Q0) = Nothing


npushr' :: NLayered n Pair a ->
           S4 a n lexposure R0Exposed ->
           S4 a n lexposure R2Exposed
npushr' a (S4 l1 l3 l4) = case l1 of
  L1L (Level (LH1 l) (RH1 r)) m1 ->
    pushlevel (LevelUM (Level (LH1 l) (RH2 (Pair r a)))) (S4 m1 l3 l4)
  L1E -> case l3 of
    L3R (Level (LH1 l) (RH0 ())) m1 m2 m3 ->
      pushlevel (LevelUU (Level (LH1 l) (RH1 a))) $ case m2 of
        L2RE -> (S4 m1 m3 l4)
        L2RL (Level (LH1 kl) kr) n1 n2 ->
          S4 m1 (L3R (Level (LH1 kl) kr) n1 n2 m3) l4
    L3L (Level l (RH1 r)) m1 m2 m3 ->
      pushlevel (LevelMM (Level l (RH2 (Pair r a)))) $ case m2 of
        L2LE -> S4 m1 m3 l4
        L2LL (Level kl (RH1 kr)) n1 n2 ->
          S4 m1 (L3L (Level kl (RH1 kr)) n1 n2 m3) l4
    L3E -> case l4 of
      L4 (Level l (RH0 ())) rest ->
        pushlevel (LevelMU (Level l (RH1 a))) rest
      L4E (Final1 b) ->       S4 L1E L3E (L4E (Final2 b a))
      L4E (Final2 b c) ->     S4 L1E L3E (L4E (Final3 b c a))
      L4E (Final3 b c d) ->   S4 L1E L3E (L4E (Final4 b c d a))
      L4E (Final4 b c d e) -> S4 L1E L3E (L4E (Final5 b c d e a))
      L4E (Final5 b p q r s) -> S4 (L1L (Level (LH1 b) (RH1 a)) L1E)
        L3E (L4E (Final2 (LN (Pair p q)) (LN (Pair r s))))

npushr :: NLayered n Pair a ->
          Queue' a n lexposure R0Exposed ->
          Queue' a n lexposure R2Exposed
npushr a Q0 = QN (S4 L1E L3E (L4E (Final1 a)))
npushr a (QN q) = QN (npushr' a q)

fix2r :: Queue' a n lexposure R2Exposed ->
         Queue' a n lexposure R0Exposed
fix2r Q0 = Q0
fix2r (QN (S4 l1 l3 l4)) = QN $ case l3 of
  L3R (Level (LH1 l) (RH2 r)) m1 m2 m3 ->
    bestowR l1 (Level (LH1 l) (RH0 ())) $ npushr' (LN r) $ case m2 of
      L2RE -> (S4 m1 m3 l4)
      L2RL (Level (LH1 kl) kr) n1 n2 ->
        S4 m1 (L3R (Level (LH1 kl) kr) n1 n2 m3) l4
  L3L (Level kl (RH1 kr)) m1 m2 m3 -> case m3 of
    L3R (Level (LH1 l) (RH2 r)) n1 n2 n3 -> case n2 of
      L2RL (Level (LH1 il) (RH0 ())) o1 o2 ->
        case npushr' (LN r) (S4 n1 (L3R (Level (LH1 il) (RH0 ())) o1 o2 n3) l4) of
        S4 p1 p3 p4 -> S4 l1 (L3L (Level kl (RH1 kr)) m1 m2 result) p4 where
          result = case p3 of
            L3E -> L3R (Level (LH1 l) (RH0 ())) p1 L2RE L3E
            q3@(L3L _ _ _ _) -> L3R (Level (LH1 l) (RH0 ())) p1 L2RE q3
            (L3R inner q1 q2 q3) ->
              L3R (Level (LH1 l) (RH0 ())) p1 (L2RL inner q1 q2) q3
      L2RE -> case npushr' (LN r) (S4 n1 n3 l4) of
        S4 o1 o3 o4 -> S4 l1 (L3L (Level kl (RH1 kr)) m1 m2 result) o4 where
          result = case o3 of
            L3E -> (L3R (Level (LH1 l) (RH0 ())) o1 L2RE L3E)
            p3@(L3L _ _ _ _) -> (L3R (Level (LH1 l) (RH0 ())) o1 L2RE p3)
            L3R inner p1 p2 p3 ->
              (L3R (Level (LH1 l) (RH0 ())) o1 (L2RL inner p1 p2) p3)
    L3E -> S4 l1 (L3L (Level kl (RH1 kr)) m1 m2 L3E) $ case l4 of
      L4 (Level l (RH2 r)) rest ->
        L4 (Level l (RH0 ())) (npushr' (LN r) rest)
      L4E final -> L4E final
  L3E -> S4 l1 L3E $ case l4 of
    L4 (Level l (RH2 r)) rest ->
      L4 (Level l (RH0 ())) (npushr' (LN r) rest)
    L4E final -> L4E final

pushr :: a -> Queue a -> Queue a
pushr a (Q00 q) = Q02 (npushr (L0 a) q)
pushr a (Q20 q) = Q22 (npushr (L0 a) q)
pushr a (Q02 q) = Q02 (npushr (L0 a) (fix2r q))
pushr a (Q22 q) = Q22 (npushr (L0 a) (fix2r q))


npopr :: S4 a n lexposure R2Exposed ->
         (NLayered n Pair a, Queue' a n lexposure R0Exposed)
npopr (S4 l1 l3 l4) = case l1 of
  L1L (Level (LH1 l) (RH1 a)) m1 -> (a, QN rest) where
    rest = pushlevel (LevelUM (Level (LH1 l) (RH0 ()))) (S4 m1 l3 l4)
  L1E -> case l3 of
    L3R (Level (LH1 l) (RH2 (Pair r a))) m1 m2 m3 -> (a, QN rest) where
      rest = pushlevel (LevelUU (Level (LH1 l) (RH1 r))) $ case m2 of
        L2RE -> S4 m1 m3 l4
        L2RL (Level (LH1 kl) kr) n1 n2 ->
          S4 m1 (L3R (Level (LH1 kl) kr) n1 n2 m3) l4
    L3L (Level l (RH1 a)) m1 m2 m3 -> (a, QN rest) where
      rest = pushlevel (LevelMM (Level l (RH0 ()))) $ case m2 of
        L2LE -> S4 m1 m3 l4
        L2LL (Level kl (RH1 kr)) n1 n2 ->
          S4 m1 (L3L (Level kl (RH1 kr)) n1 n2 m3) l4
    L3E -> case l4 of
      L4 (Level l (RH2 (Pair r a))) inner -> (a, QN rest) where
        rest = pushlevel (LevelMU (Level l (RH1 r))) inner
      L4E (Final5 v w x y z) -> (z, QN (S4 L1E L3E (L4E (Final4 v w x y))))
      L4E (Final4   w x y z) -> (z, QN (S4 L1E L3E (L4E (Final3   w x y))))
      L4E (Final3     x y z) -> (z, QN (S4 L1E L3E (L4E (Final2     x y))))
      L4E (Final2       y z) -> (z, QN (S4 L1E L3E (L4E (Final1       y))))
      L4E (Final1         z) -> (z, Q0)


fix0r :: Queue' a n lexposure R0Exposed ->
         Queue' a n lexposure R2Exposed
fix0r Q0 = Q0
fix0r (QN (S4 l1 l3 l4)) = QN $ case l3 of
  L3R (Level (LH1 l) (RH0 ())) m1 m2 m3 ->
    case npopr poppee of
      (LN r, QN result) -> bestowR l1 (Level (LH1 l) (RH2 r)) result
      (LN (Pair a b), Q0) -> S4 l1 L3E (L4E (Final3 l a b))
    where
      poppee = case m2 of
        L2RE -> S4 m1 m3 l4
        L2RL (Level (LH1 kl) kr) n1 n2 ->
          S4 m1 (L3R (Level (LH1 kl) kr) n1 n2 m3) l4
  L3L (Level kl (RH1 kr)) m1 m2 m3 -> case m3 of
    L3R (Level (LH1 l) (RH0 ())) n1 n2 n3 -> case n2 of
      L2RL (Level (LH1 il) (RH2 r)) o1 o2 ->
        case npopr (S4 n1 (L3R (Level (LH1 il) (RH2 r)) o1 o2 n3) l4) of
          (LN r, QN (S4 p1 p3 p4)) ->
            S4 l1 (L3L (Level kl (RH1 kr)) m1 m2 result) p4 where
              result = case p3 of
                L3E -> L3R (Level (LH1 l) (RH2 r)) p1 L2RE L3E
                q3@(L3L _ _ _ _) -> L3R (Level (LH1 l) (RH2 r)) p1 L2RE q3
                L3R inner q1 q2 q3 ->
                  L3R (Level (LH1 l) (RH2 r)) p1 (L2RL inner q1 q2) q3
          (LN (Pair a b), Q0) ->
            S4 l1 (L3L (Level kl (RH1 kr)) m1 m2 L3E) (L4E (Final3 l a b))
      L2RE -> case npopr (S4 n1 n3 l4) of
        (LN r, QN (S4 o1 o3 o4)) ->
          S4 l1 (L3L (Level kl (RH1 kr)) m1 m2 result) o4 where
            result = case o3 of
              L3E -> L3R (Level (LH1 l) (RH2 r)) o1 L2RE L3E
              p3@(L3L _ _ _ _) -> L3R (Level (LH1 l) (RH2 r)) o1 L2RE p3
              L3R inner p1 p2 p3 ->
                L3R (Level (LH1 l) (RH2 r)) o1 (L2RL inner p1 p2) p3
        (LN (Pair a b), Q0) ->
          S4 l1 (L3L (Level kl (RH1 kr)) m1 m2 L3E) (L4E (Final3 l a b))
    L3E -> S4 l1 (L3L (Level kl (RH1 kr)) m1 m2 L3E) $ case l4 of
      L4 (Level l (RH0 ())) rest -> case npopr rest of
          (LN r, QN new) -> L4 (Level l (RH2 r)) new
          (LN (Pair a b), Q0) -> case l of
            LH0 () -> L4E (Final2 a b)
            LH2 (Pair q r) -> L4E (Final4 q r a b)
      L4E final -> L4E final
  L3E -> S4 l1 L3E $ case l4 of
    L4 (Level l (RH0 ())) rest -> case npopr rest of
      (LN r, QN new) -> L4 (Level l (RH2 r)) new
      (LN (Pair a b), Q0) -> case l of
        LH0 () -> L4E (Final2 a b)
        LH2 (Pair q r) -> L4E (Final4 q r a b)
    L4E final -> L4E final


popr :: Queue a -> Maybe (a, Queue a)
popr (Q00 q) = popr (Q02 (fix0r q))
popr (Q20 q) = popr (Q22 (fix0r q))
popr (Q02 (QN q)) = Just $ case npopr q of
  (L0 a, new) -> (a, Q00 new)
popr (Q22 (QN q)) = Just $ case npopr q of
  (L0 a, new) -> (a, Q20 new)
popr (Q02 Q0) = Nothing
popr (Q22 Q0) = Nothing
