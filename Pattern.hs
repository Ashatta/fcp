{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Pattern where

type family (:++:) a b
type instance () :++: l = l
type instance (h, t) :++: l = (h, t :++: l)

type Uncurried vars r = vars -> r

type family Curried vars r
type instance Curried () r = r
type instance Curried (h, t) r = h -> Curried t r

type Uncurry vars r = Curried vars r -> Uncurried vars r

data Proxy a
proxy :: Proxy a
proxy = undefined

data a :==: b where
    Equal :: a :==: a

data ListD a where
    ListD :: List' a => ListD a

class List' a where
    closure :: forall b. List' b => Proxy a -> Proxy b -> ListD (a :++: b)
    assoc :: forall b c. Proxy a -> Proxy b -> Proxy c -> ((a :++: (b :++: c)) :==: ((a :++: b) :++: c))
    rightIdent :: Proxy a -> (a :++: ()) :==: a

instance List' () where
    closure _ _ = ListD
    assoc _ _ _ = Equal
    rightIdent _ = Equal

instance List' t => List' (h, t) where
    closure _ b = case closure (proxy :: Proxy t) b of
                      ListD -> ListD
    assoc _ b c = case assoc (proxy :: Proxy t) b c of
                      Equal -> Equal
    rightIdent _ = case rightIdent (proxy :: Proxy t) of
                       Equal -> Equal


newtype UncurryBuilder vars = UncurryBuilder { build :: forall vars' r. 
    Proxy vars' -> Uncurry vars' r -> Uncurry (vars :++: vars') r }

zeroC :: UncurryBuilder ()
zeroC = UncurryBuilder (\_ -> id)
succC :: UncurryBuilder (a, ())
succC = UncurryBuilder (\_ -> succ')
    where succ' n f = \(x, xs) -> n (f x) xs
appendC :: forall as bs. List' as => UncurryBuilder as -> UncurryBuilder bs -> UncurryBuilder (as :++: bs)
appendC (UncurryBuilder conv1) (UncurryBuilder conv2) = UncurryBuilder (\(_ :: Proxy vars') ->
    case assoc (proxy :: Proxy as) (proxy :: Proxy bs) (proxy :: Proxy vars') of
        Equal -> conv1 (proxy :: Proxy (bs :++: vars')) . conv2 (proxy :: Proxy vars'))

newtype Push vars = Push { push :: forall vars' r. 
    Proxy vars' -> 
    (Uncurried (vars :++: vars') r) -> 
    (forall s. s -> r) -> 
    vars' -> 
    r 
}

nil :: Push ()
nil = Push (\_ cs _ vars -> cs vars)

one :: a -> Push (a, ())
one v = Push (\_ cs _ args -> cs (v, args))

(#) :: forall as bs. List' as => Push as -> Push bs -> Push (as :++: bs)
(Push m) # (Push n) = Push (\(_ :: Proxy vars') ->
                          case assoc (proxy :: Proxy as) (proxy :: Proxy bs) (proxy :: Proxy vars') of
                              Equal -> m (proxy :: Proxy (bs :++: vars')) `append'` n (proxy :: Proxy vars'))
                      where n `append'` m = \cs cf args -> m (n cs cf) cf args    

fail' :: Push vars
fail' = Push (\_ _ cf _ -> cf ())

catch :: Push as -> Push as -> Push as
(Push m) `catch` (Push n) = Push (\p cs cf args -> (m p) cs (\_ -> (n p) cs cf args) args)

data Pattern vars val = List' vars => Pattern (UncurryBuilder vars) (val -> Push vars)

newtype Clause v r = Clause { run :: v -> (forall s. s -> r) -> r }

infixl 2 ->>
infixl 1 |||

(->>) :: forall vars a r. Pattern vars a -> Curried vars r -> Clause a r
(Pattern pC pV) ->> f = Clause (case rightIdent (proxy :: Proxy vars) of
                                    Equal -> \v cf -> push (pV v) (proxy :: Proxy ()) (build pC (proxy :: Proxy ()) zero f) cf ())
          where zero f = \() -> f

(|||) :: Clause a r -> Clause a r -> Clause a r
c1 ||| c2 = Clause (\v cf -> run c1 v (\_ -> run c2 v cf))

match :: a -> Clause a r -> r
match v clauses = run clauses v (\_ -> error "pattern mismatch")

------------- basic patterns -------------------------

var :: Pattern (a, ()) a
var = Pattern succC one

cst :: Eq a => a -> Pattern () a
cst v = Pattern zeroC (\v' -> if v == v' then nil else fail')

pair :: forall as bs a b. Pattern as a -> Pattern bs b -> Pattern (as :++: bs) (a, b)
pair (Pattern pC pV) (Pattern qC qV) = case closure (proxy :: Proxy as) (proxy :: Proxy bs) of
                                           ListD -> Pattern (pC `appendC` qC) (\(a, b) -> pV a # qV b)

--------- disjunction -----------------

none = Pattern zeroC (\_ -> fail')
(Pattern pC pV) \/ (Pattern qC qV) = Pattern pC (\v -> pV v `catch` qV v)

--------- conjunction -------------------

any' = Pattern zeroC (\_ -> nil)
(/\) :: forall as bs a. Pattern as a -> Pattern bs a -> Pattern (as :++: bs) a
(Pattern pC pV) /\ (Pattern qC qV) = case closure (proxy :: Proxy as) (proxy :: Proxy bs) of
                                         ListD -> Pattern (pC `appendC` qC) (\v -> pV v # qV v)

--------- predicates --------------------

is p = Pattern zeroC (\v -> if p v then nil else fail')

--------------------------------------------------------------------------
