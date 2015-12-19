{-# LANGUAGE MultiParamTypeClasses #-} 
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Pattern

class List l a where
    head' :: l a -> a
    tail' :: l a -> l a
    isEmpty :: l a -> Bool

instance List [] a where
    head' = head
    tail' = tail
    isEmpty = null

emptyList :: List l a => Pattern () (l a)
emptyList = is isEmpty

list :: forall as bs l a. List l a => Pattern as a -> Pattern bs (l a) -> Pattern (as :++: bs) (l a)
list (Pattern hC hV) (Pattern tC tV) = 
    case closure (proxy :: Proxy as) (proxy :: Proxy bs) of
        ListD -> Pattern (hC `appendC` tC) (\v -> if isEmpty v then fail' else hV (head' v) # tV (tail' v))

reify :: [Clause v r] -> v -> r
reify cl v = match v $ foldr (|||) (any' ->> error "no pattern matched the value") cl

listMatchers f g = [\fold acc -> emptyList ->> f fold acc, \fold acc -> list var var ->> g fold acc]

fold f g acc xs = reify (map (\f -> f fold' acc) dict) xs
    where dict = listMatchers f g
          fold' = fold f g
