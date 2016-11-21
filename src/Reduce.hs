{-# Language FlexibleInstances , TypeSynonymInstances #-}
{-|
Module      : Reduce
Description : Recuctions of a Rabin acceptance condition
Copyright   : Clara Waldmann, 2016

Reductions of a Rabin acceptance condition dependent and independent of the transition system of the automaton.
-}
module Reduce (
    -- * Reductions Independent of the Transition System
    set_reduce, set_sat, set_irredundant,
    -- * Reductions Dependent of the Transition System
    SingletonRabinpair(..), SingletonDRA(..),
    top_reduce, top_sat, top_irredundant,
    -- * Splitting and Combinig Pairs
    set_split, set_combine, top_split, top_combine,
    -- * Checks
    is_compact, is_scc,
    -- * Conversion Between DRA and Singleton DRA
    toSDRA, toDRA,
    -- * Example Rabin Automata
    exdra, exdra1, exdra2
    
) where 

import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Map as M
import Control.Monad (guard)

import Data.Graph.Inductive

import OmegaAutomata.Automata

import Data.Poset

instance Ord q => Poset (Rabinpair q) where
    leq (e1,f1) (e2,f2) = (S.isSubsetOf e2 e1) && (S.isSubsetOf f1 f2)

ismaximal :: Poset a => [a] -> a -> Bool
ismaximal xs m = all (\y -> (y == m) || m </=> y || not (leq m y)) xs
    
maxels :: Poset a => [a] -> [a]
maxels xs = filter (ismaximal xs) xs
    
-- | type for a Rabin pair whose final set is singleton
data SingletonRabinpair q = SingletonRabinpair {
    infinite :: q,
    finite :: S.Set q
    }
    deriving (Eq, Ord, Show)
-- | type for Rabin automata where each final set is singleton
type SingletonDRA q a l = Automat q a l [SingletonRabinpair q]
    

new_acceptance :: DRA q a l -> ([Rabinpair q] -> [Rabinpair q]) -> DRA q a l
new_acceptance dra new =
    let acc = accept dra
    in dra {accept = new acc}

    
{- | reduction of a pair by (E,F) -> (E, F \\ E) 

>>> accept $ set_reduce exdra
[(fromList [3],fromList [1,2])
,(fromList [1,2,3],fromList [])
,(fromList [],fromList [1,2])
]
-}
set_reduce :: Ord q => DRA q a l -> DRA q a l
set_reduce dra = new_acceptance dra ((\(e,f) -> (e, f S.\\ e)) <$>)

{- | remove unsatisfiable pairs (where the final set is empty)

>>> accept  $ set_sat $ set_reduce exdra
[(fromList [3],fromList [1,2]),(fromList [],fromList [1,2])]
-}
set_sat :: Eq q => DRA q a l -> DRA q a l
set_sat dra = 
    new_acceptance dra (filter (\(_,f) -> S.empty /= f))

-- | split final sets into singletons
set_split :: DRA q a l -> SingletonDRA q a l
set_split dra = 
    let acc = accept dra
    in dra {accept = do
                (e,f) <- acc
                q <- S.toList f
                return $ SingletonRabinpair q e
            }
        
-- | combine pair with same excluded set by taking the union of the final sets
set_combine :: Ord q => DRA q a l -> DRA q a l
set_combine dra =
    new_acceptance dra (M.toList . M.fromListWith S.union)
    
{- | remove redundant pairs

>>> accept $ set_irredundant $ set_sat $ set_reduce exdra
[(fromList [],fromList [1,2])]
-}
set_irredundant :: Ord q => DRA q a l -> DRA q a l
set_irredundant dra = 
    new_acceptance dra maxels
    

{- | reduce a pair (Rabin automaton has to be compact)

>>> accept$ top_reduce $ exdra2 {accept = [(S.fromList [3],S.fromList [1]),(S.fromList [3],S.fromList [2])]}
[(fromList [],fromList [1]),(fromList [],fromList [2])]
-}
top_reduce :: Ord q => DRA q a l  -> DRA q a l
top_reduce dra = 
    new_acceptance dra ((top_pair_reduce dra)<$>)
    
sccs_dra :: Ord q => DRA q a l -> [[q]]
sccs_dra dra = map (\ns -> toState dra <$> ns) (scc $ graph dra)
    
-- | compute the SCCs of the Rabin automaton that intersect the set
sccs_of_f :: Ord q => DRA q a l -> S.Set q -> [S.Set q]
sccs_of_f dra f = if S.null f 
                     then []
                     else filter (\scc -> not $ S.null $ S.intersection f scc) (S.fromList <$> sccs_dra dra) 
    
s :: Ord q => DRA q a l -> S.Set q -> [S.Set q]
s dra f =
    {-let fscc = case sccs_of_f dra f of
            [] -> S.empty
            [scc] -> scc
    in-} sccs_of_f dra f
    
toRabinpair :: SingletonRabinpair q -> Rabinpair q
toRabinpair (SingletonRabinpair q e) = (e, S.singleton q)

toSingletonRabinpair :: Show q => Rabinpair q -> SingletonRabinpair q
toSingletonRabinpair (e,f) =
    case S.toList f of 
        [q]-> SingletonRabinpair{infinite = q, finite = e}
        _ -> error (show f ++ " not singleton")

toDRA :: SingletonDRA q a l -> DRA q a l
toDRA sdra = sdra {accept = toRabinpair <$> accept sdra }

-- | only works for automata where all final sets are singletons
toSDRA :: Show q => DRA q a l -> SingletonDRA q a l
toSDRA dra = dra {accept =  toSingletonRabinpair <$> accept dra }

        
-- | S_R (E, {q})
s_pair :: Ord q => SingletonDRA q a l -> SingletonRabinpair q -> S.Set q
s_pair dra p@(SingletonRabinpair q e) =
    let greq = g (toDRA dra) (toRabinpair p)
        qscc = case filter ((toNode dra q) `elem`) $ scc greq of
                    [] -> []
                    [scc] -> scc
    in S.fromList $ toState dra <$> qscc
    
-- G_R (E, F) for (E,F) compact
g :: Ord q => DRA q a l -> Rabinpair q -> Gr l a
g dra (e,f) =
    let srf = case s dra f of
                [] -> S.empty
                [scc] -> scc
        srf_g = subgraph ((toNode dra) <$> S.toList srf) (graph dra)
    in delNodes ((toNode dra) <$> S.toList e) srf_g
    
cyclic_sccs :: Gr a b -> [[Node]]
cyclic_sccs g = 
    let sccs = scc g
        (prob, cyc) = L.partition (\ns -> 1 == length ns) sccs
        c = filter (\[n] -> hasNeighbor g n n) prob
    in c ++ cyc
    
-- is there a cycle in G_R (E, F) visiting F for (E,F) compact ? 
visits_f :: Ord q => DRA q a l -> Rabinpair q -> Bool
visits_f dra p@(e,f) =
    let gref = g dra p
        cycs = cyclic_sccs gref
    in any (\ns -> not $ S.null $ S.intersection f $ S.fromList $ (toState dra) <$> ns) cycs
    

top_pair_reduce :: Ord q => DRA q a l -> Rabinpair q -> Rabinpair q
top_pair_reduce dra (e,f) = 
    let [srf] = s dra f 
    in (S.intersection e srf, f)
    
{- | remove unsatisfiable pairs (Rabin automaton has to be compact)

>>> accept $ top_sat $ toDRA $ set_split exdra1
[(fromList [2],fromList [1])
,(fromList [3],fromList [2])
,(fromList [1],fromList [2])]
-}
top_sat :: Ord q => DRA q a l -> DRA q a l
top_sat dra = new_acceptance dra (filter (visits_f dra))
    
-- | split pairs to become compact
top_split :: Ord q => DRA q a l -> DRA q a l
top_split dra = new_acceptance dra 
        (\ps -> do 
            p@(e,f) <- ps
            sc <- sccs_of_f dra f
            return $ (e, S.intersection f sc)
        )
        
-- | combine pairs in different SCCs (only for strongly compact Rabin automata)
top_combine :: Ord q => DRA q a l -> DRA q a l
top_combine dra =
    let sccmap = M.fromListWith (++) 
            $ (\(e,f) -> (sccs_of_f dra f, [(e,f)])) 
                <$> accept dra
        sccnrmap = M.map (zip [0..]) sccmap
        nm = M.fromListWith (\(e1,f1) (e2,f2) -> (S.union e1 e2, S.union f1 f2)) $ concat $ M.elems sccnrmap
    in dra {accept = M.elems nm}


setismax :: Ord q => S.Set q -> [S.Set q] -> Bool
setismax x xs = all (\y -> y == x || not ( S.isSubsetOf x y)) xs

{- | remove redundant pairs
top_irredundant :: (Ord q, Eq l, Ord a) => SingletonDRA q a l -> SingletonDRA q a l

>>> accept $ top_irredundant $ toSDRA $ top_sat $ toDRA $ set_split exdra1
[SingletonRabinpair {infinite = 1, finite = fromList [2]}
,SingletonRabinpair {infinite = 2, finite = fromList [3]}]

-}
top_irredundant dra = 
    let acc = (\p@(SingletonRabinpair q e) 
                -> (q, [(s_pair dra p, p)]))
              <$> accept dra
        comparemap = M.fromListWith (++) acc
        minmap = M.map ( M.fromListWith min ) comparemap
        nm = M.map 
            (\ps -> M.filterWithKey 
                 (\s _ -> (setismax s $ M.keys ps)) 
                ps) 
            minmap
    in dra {accept = concat ( M.elems <$> (M.elems nm))}

-- | is the Rabin automaton compact? (final sets contained in one SCC)
--
-- >>> is_compact exdra2
-- False
is_compact :: Ord q => DRA q a l -> Bool
is_compact dra = all (\(e,f) -> let sf = sccs_of_f dra f 
                                in (length sf == 0 || length sf == 1))
                    $ accept dra

-- | is the Rabin automaton strongly compact? (each pair contained in one SCC)
--
-- >>> is_scc  exdra1
-- True
is_scc :: Ord q => DRA q a l -> Bool
is_scc dra = is_compact dra &&
    (all (\(e,f) -> sccs_of_f dra e == [] || sccs_of_f dra e == sccs_of_f dra f ) 
        $ accept dra )
                  
{- | Example Rabin automaton (acceptance condition from Example 6.6 in the thesis)

@ exdra = makeAutomat 
    [(1,()), (2,()), (3,())] 
    [(1,(),1), (1,(),2), (2,(),1), (2,(),2), (1,(),3), (3,(),2)] 
    [1] 
    [ (S.fromList [3], S.fromList [1,2])
    , (S.fromList [1,2,3], S.fromList [2])
    , (S.fromList [], S.fromList [1,2])
    ]
@
-}
exdra :: DRA Int () ()
exdra = makeAutomat 
    [(1,()), (2,()), (3,())] 
    [(1,(),1), (1,(),2), (2,(),1), (2,(),2), (1,(),3), (3,(),2)] 
    [1] 
    [ (S.fromList [3], S.fromList [1,2])
    , (S.fromList [1,2,3], S.fromList [2])
    , (S.fromList [], S.fromList [1,2])
    ]
    
{- | Example Rabin automaton (acceptance condition taken from Example 6.13 in the thesis)

@ exdra1 = makeAutomat 
    [(1,()), (2,()), (3,())] 
    [(1,(),1), (1,(),2), (2,(),1), (2,(),2), (1,(),3), (3,(),2)] 
    [1] 
    [ (S.fromList [2], S.fromList [1])
    , (S.fromList [3], S.fromList [2])
    , (S.fromList [1], S.fromList [2,3])
    ]
@
-}
exdra1 :: DRA Int () ()
exdra1 = makeAutomat 
    [(1,()), (2,()), (3,())] 
    [(1,(),1), (1,(),2), (2,(),1), (2,(),2), (1,(),3), (3,(),2)] 
    [1] 
    [ (S.fromList [2], S.fromList [1])
    , (S.fromList [3], S.fromList [2])
    , (S.fromList [1], S.fromList [2,3])
    ]

    
{- | example Rabin automaton (from Example 6.18 in the thesis)

@ exdra2 = makeAutomat
    [(1,()), (2,()), (3,())]
    [(1,(),1), (1,(),2), (2,(),2), (1,(),3), (3,(),2)]
    [1]
    [(S.fromList [3], S.fromList [1,2])]
@
-}
exdra2 :: DRA Int () ()
exdra2 = makeAutomat
    [(1,()), (2,()), (3,())]
    [(1,(),1), (1,(),2), (2,(),2), (1,(),3), (3,(),2)]
    [1]
    [(S.fromList [2], S.fromList [1,2])]
    
