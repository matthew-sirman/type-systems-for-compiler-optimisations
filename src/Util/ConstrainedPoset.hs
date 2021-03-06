{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, Rank2Types #-}
module Util.ConstrainedPoset
     ( ConstrainedPoset
     , FixedCorePoset(..)
     -- Construction
     , empty
     , fromList
     -- Modification
     , addLeq
     , addLeqs
     -- Query
     , leq
     , equivalent
     , maybeLeq
     , unlimited
     ) where

import Data.Hashable (Hashable)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.Bifunctor (bimap)
import Control.Lens
import Control.Monad.Cont
import Control.Monad.State

data RelationElem core a = RelationElem
    { _edges :: S.HashSet a
    , _bound :: core
    }
    deriving Show

makeLenses ''RelationElem

newtype ConstrainedPoset core a = ConstrainedPoset
    { _lessThan :: M.HashMap a (RelationElem core a, RelationElem core a)
    }
    deriving Show

makeLenses ''ConstrainedPoset

data TightenResult result
    = Failed
    | NoChange
    | Result result

instance Functor TightenResult where
    fmap _ Failed = Failed
    fmap _ NoChange = NoChange
    fmap f (Result r) = Result (f r)

instance Applicative TightenResult where
    pure = Result
    Failed <*> _ = Failed
    NoChange <*> _ = NoChange
    _ <*> Failed = Failed
    _ <*> NoChange = NoChange
    (Result f) <*> (Result x) = Result (f x)

instance Monad TightenResult where
    Failed >>= _ = Failed
    NoChange >>= _ = NoChange
    (Result a) >>= f = f a

infix 4 <=?
class FixedCorePoset core a | core -> a, a -> core where
    (<=?) :: core -> core -> Bool
    bottom :: core
    top :: core
    lub :: core -> core -> core
    glb :: core -> core -> core
    unembed :: a -> Maybe core
    unconj :: a -> Maybe (a, a)

--------------------------------
--------------------------------
----      Construction      ----
--------------------------------
--------------------------------

empty :: ConstrainedPoset c a
empty = ConstrainedPoset M.empty

fromList :: (Eq core, Eq a, Hashable a, FixedCorePoset core a) => [(a, a)] -> Maybe (ConstrainedPoset core a)
fromList = addLeqs empty

--------------------------------
--------------------------------
----      Modification      ----
--------------------------------
--------------------------------

addLeq :: forall core a. (Eq core, Eq a, Hashable a, FixedCorePoset core a)
       => a -> a -> ConstrainedPoset core a -> Maybe (ConstrainedPoset core a)
addLeq l r setInit
    | l == r = Just setInit
    | otherwise =
        let setLeftCore = case unembed l of
                            Just c -> (lessThan %~ M.insertWith const l (RelationElem S.empty c, RelationElem S.empty c)) setInit
                            Nothing -> setInit
            set         = case unembed r of
                            Just c -> (lessThan %~ M.insertWith const r (RelationElem S.empty c, RelationElem S.empty c)) setLeftCore
                            Nothing -> setLeftCore
        in
        case (M.lookup l (set ^. lessThan), M.lookup r (set ^. lessThan)) of
          (Nothing, Nothing) -> Just $ (lessThan %~ M.insert l (RelationElem (S.singleton r) bottom, RelationElem S.empty top) 
                                                  . M.insert r (RelationElem S.empty bottom, RelationElem (S.singleton l) top)) set
          (Just p, Nothing)  -> Just $ (lessThan %~ M.adjust (_1.edges %~ S.insert r) l 
                                                  . M.insert r (RelationElem S.empty (p ^. _1.bound), RelationElem (S.singleton l) top)) set
          (Nothing, Just q)  -> Just $ (lessThan %~ M.insert l (RelationElem (S.singleton r) bottom, RelationElem S.empty (q ^. _2.bound))
                                                  . M.adjust (_2.edges %~ S.insert l) r) set
          (Just _, Just _)   -> do
              let set' = (lessThan %~ M.adjust (_1.edges %~ S.insert r) l
                                    . M.adjust (_2.edges %~ S.insert l) r) set
              traverseTighten _1 lub l r set' >>= traverseTighten _2 glb r l
        where
            traverseTighten :: Lens' (RelationElem core a, RelationElem core a) (RelationElem core a) -> (core -> core -> core)
                            -> a -> a -> ConstrainedPoset core a -> Maybe (ConstrainedPoset core a)
            traverseTighten selector joiner p q set = snd <$> execStateT (traverseTighten' p q) (S.empty, set)
                where
                    traverseTighten' :: a -> a -> StateT (S.HashSet a, ConstrainedPoset core a) Maybe ()
                    traverseTighten' from to = do
                        (visited, current) <- get
                        toElem <- lift $ M.lookup to (current ^. lessThan)
                        case tighten selector joiner from to current of
                          Failed -> lift Nothing
                          NoChange -> pure ()
                          Result updatedSet -> do
                              let neighbours = toElem ^. selector.edges
                              put (visited `S.union` neighbours, updatedSet)
                              forM_ (neighbours `S.difference` visited) (traverseTighten' to)

            traverseTightenBackward set p q = snd <$> execStateT (traverseTighten' p q) (S.empty, set)
                where
                    traverseTighten' :: a -> a -> StateT (S.HashSet a, ConstrainedPoset core a) Maybe ()
                    traverseTighten' from to = do
                        undefined

tighten :: (Eq core, Eq a, Hashable a, FixedCorePoset core a)
        => Lens' (RelationElem core a, RelationElem core a) (RelationElem core a)
        -> (core -> core -> core)
        -> a -> a -> ConstrainedPoset core a -> TightenResult (ConstrainedPoset core a)
tighten selector joiner left right set = do
    leftElem <- (^. selector) <$> maybe Failed pure (M.lookup left (set ^. lessThan))
    rightElem <- (^. selector) <$> maybe Failed pure (M.lookup right (set ^. lessThan))
    let lb' = (leftElem ^. bound) `joiner` (rightElem ^. bound)
    case unembed right of
      Just ub -> unless (lb' <=? ub) Failed
      Nothing -> pure ()
    when (lb' == rightElem ^. bound) NoChange
    let set' = (lessThan %~ M.adjust (selector.bound .~ lb') right) set
    (lower, upper) <- bimap (^. bound) (^. bound) <$> maybe Failed pure (M.lookup right (set' ^. lessThan))
    unless (lower <=? upper) Failed
    pure set'

addLeqs :: (Eq core, Eq a, Hashable a, FixedCorePoset core a)
        => ConstrainedPoset core a -> [(a, a)] -> Maybe (ConstrainedPoset core a)
addLeqs = foldM (flip $ uncurry addLeq)

-------------------------
-------------------------
----      Query      ----
-------------------------
-------------------------

leq :: (Eq a, Hashable a, FixedCorePoset core a) => a -> a -> ConstrainedPoset core a -> Bool
leq a b p = case (unembed a, unembed b) of
              (Just a', Just b') -> a' <=? b'
              _ -> reachable a b p

reachable :: forall core a. (Eq a, Hashable a) => a -> a -> ConstrainedPoset core a -> Bool
reachable lhs rhs set
    | lhs == rhs = True
    | otherwise = (`evalState` S.empty) $
        (`runContT` pure) $ 
            callCC $ \succeed -> do
                reachable' lhs rhs succeed
                pure False
    where
        reachable' :: a -> a -> (Bool -> ContT Bool (State (S.HashSet a)) ()) -> ContT Bool (State (S.HashSet a)) ()
        reachable' a b succeed
            | b `S.member` neighbours = succeed True
            | otherwise = do
                marked <- get
                modify (S.union neighbours)
                mapM_ (\n -> reachable' n b succeed) (neighbours `S.difference` marked)
            where
                neighbours :: S.HashSet a
                neighbours = case M.lookup a (set ^. lessThan) of
                               Just elem -> elem ^. _1.edges
                               Nothing -> S.empty

equivalent :: (Eq a, Hashable a) => a -> a -> ConstrainedPoset core a -> Bool
equivalent lhs rhs set
    | lhs == rhs = True
    | otherwise = reachable lhs rhs set && reachable rhs lhs set

maybeLeq :: (Eq a, Hashable a, FixedCorePoset core a) => a -> core -> ConstrainedPoset core a -> Bool
maybeLeq v c poset = case M.lookup v (poset ^. lessThan) of
                       Just elem -> (elem ^. _1.bound) <=? c
                       Nothing -> 
                           case unembed v of
                             Just c' -> c' <=? c
                             Nothing ->
                                 case unconj v of
                                   Just (l, r) -> maybeLeq l c poset || maybeLeq r c poset
                                   Nothing -> True

unlimited :: (Eq a, Hashable a, Eq core, FixedCorePoset core a) => a -> ConstrainedPoset core a -> Bool
unlimited v set = case M.lookup v (set ^. lessThan) of
                    Just elem -> (elem ^. _1.bound == bottom) && (elem ^. _2.bound == top)
                    Nothing ->
                        case unembed v of
                          Just _ -> False
                          Nothing ->
                              case unconj v of
                                Just (l, r) -> unlimited l set && unlimited r set
                                Nothing -> True

