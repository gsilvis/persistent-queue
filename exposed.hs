{-# LANGUAGE GADTs, KindSignatures #-}

data Zero
data Succ n

data NLayered n :: (* -> *) -> (* -> *) where
  L0 :: a -> NLayered Zero f a
  LN :: f (NLayered n f a) -> NLayered (Succ n) f s

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

data L4 a :: * -> * -> * -> * where
  L4E0 :: () ->
          L4 a top lexposure rexposure
  L4E1 :: NLayered top Pair a ->
          L4 a top lexposure rexposure
  L4 :: Level a top LModifying lmid lexp RModifying rmid rexp ->
        S4 a (Succ top) lmid rmid ->
        L4 a top lexp rexp

data S4 a :: * -> * -> * -> * where
  S4 :: L1 a top mid ->
        L3 a mid bot lbot ltop rbot rtop politics ->
        L4 a bot lbot rbot ->
        S4 a top ltop rtop

data Queue a = Q00 (S4 a Zero L0Exposed R0Exposed)
             | Q02 (S4 a Zero L0Exposed R2Exposed)
             | Q20 (S4 a Zero L2Exposed R0Exposed)
             | Q22 (S4 a Zero L2Exposed R2Exposed)

empty :: Queue a
empty = Q00 (S4 L1E L3E (L4E0 ()))

singleton :: a -> Queue a
singleton a = Q00 (S4 L1E L3E (L4E1 (L0 a)))

doubleton :: a -> Queue a
doubleton a =
  Q00 (S4 (L1L (Level (LH1 (L0 a)) (RH1 (L0 a))) L1E) L3E (L4E0 ()))


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


npushl :: NLayered n Pair a ->
          S4 a n L0Exposed rexposure ->
          S4 a n L2Exposed rexposure
npushl a (S4 l1 l3 l4) = case l1 of
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
      L4E0 () -> S4 L1E L3E (L4E1 a)
      L4E1 b -> S4 (L1L (Level (LH1 a) (RH1 b)) L1E) L3E (L4E0 ())


fix2l :: S4 a n L2Exposed rexposure ->
         S4 a n L0Exposed rexposure
fix2l (S4 l1 l3 l4) = case l3 of
  L3L (Level (LH2 l) (RH1 r)) m1 m2 m3 ->
    bestowL l1 (Level (LH0 ()) (RH1 r)) $ npushl (LN l) $ case m2 of
      L2LE -> (S4 m1 m3 l4)
      L2LL (Level kl (RH1 kr)) n1 n2 -> 
        S4 m1 (L3L (Level kl (RH1 kr)) n1 n2 m3) l4
  L3R (Level (LH1 kl) kr) m1 m2 m3 -> case m3 of
    L3L (Level (LH2 l) (RH1 r)) n1 n2 n3 -> case n2 of
      L2LL (Level (LH0 ()) (RH1 ir)) o1 o2 ->
        case npushl (LN l) (S4 n1 (L3L (Level (LH0 ()) (RH1 ir)) o1 o2 n3) l4) of
        S4 p1 p3 p4 -> S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 result) p4 where
          result = case p3 of
            L3E -> L3L (Level (LH0 ()) (RH1 r)) p1 L2LE L3E
            q3@(L3R _ _ _ _) -> L3L (Level (LH0 ()) (RH1 r)) p1 L2LE q3
            (L3L inner q1 q2 q3) ->
              L3L (Level (LH0 ()) (RH1 r)) p1 (L2LL inner q1 q2) q3
      L2LE -> case npushl (LN l) (S4 n1 n3 l4) of
        S4 o1 o3 o4 -> S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 result) o4 where
          result = case o3 of
            L3E -> (L3L (Level (LH0 ()) (RH1 r)) o1 L2LE L3E)
            p3@(L3R _ _ _ _) -> (L3L (Level (LH0 ()) (RH1 r)) o1 L2LE p3)
            L3L inner p1 p2 p3 ->
              (L3L (Level (LH0 ()) (RH1 r)) o1 (L2LL inner p1 p2) p3)
    L3E -> case l4 of
      L4 (Level (LH2 l) r) rest ->
        (S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 L3E) (L4 (Level (LH0 ()) r) new))
          where new = npushl (LN l) rest
      L4E0 () -> (S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 L3E) (L4E0 ()))
      L4E1 a -> (S4 l1 (L3R (Level (LH1 kl) kr) m1 m2 L3E) (L4E1 a))
  L3E -> case l4 of
    L4 (Level (LH2 l) r) rest -> case npushl (LN l) rest of
      new -> S4 l1 L3E (L4 (Level (LH0 ()) r) new)
    L4E0 () -> S4 l1 L3E (L4E0 ())
    L4E1 a -> S4 l1 L3E (L4E1 a)


pushl :: a -> Queue a -> Queue a
pushl a (Q00 q) = Q20 (npushl (L0 a) q)
pushl a (Q02 q) = Q22 (npushl (L0 a) q)
pushl a (Q20 q) = Q20 (npushl (L0 a) (fix2l q))
pushl a (Q22 q) = Q22 (npushl (L0 a) (fix2l q))
