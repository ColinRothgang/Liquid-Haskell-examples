
module Util
  ( module Data.Maybe
  , module Util
  , module Control.Applicative
  , module Data.List
  , module Data.Functor
  ) where
import Data.List(intercalate, partition)
import Prelude


import Data.Maybe
import Control.Applicative((<|>))
import Data.Functor((<&>))
import qualified Data.Bifunctor as B
type Id = String

addParens :: String -> String
-- addParens s@(c:cs) | c == '(' && last s == ')' = s
addParens s 
  | bracketed && correctlyBracketed 0 sStripped = s
  | otherwise = "(" ++s ++ ")" where
  bracketed = safeHead s == Just '(' && last s == ')'
  sStripped = if bracketed then (init . tail) s else s
  correctlyBracketed n ('(':s) = correctlyBracketed (n+1) s
  correctlyBracketed n (')':_) | n <= 0 = False
  correctlyBracketed n (')':s) = correctlyBracketed (n-1) s
  correctlyBracketed n (_:s) = correctlyBracketed n s
  correctlyBracketed n [] = True


-- Get rid of module names.
showStripped :: Show a => a -> String
showStripped = strip . show

{-@ strip :: s:String -> String @-}
strip :: String -> String
strip s = case split '.' s of
  [] -> ""
  parts -> last parts

split :: Char -> String -> [String]
split c s = case rest of
                []     -> [chunk]
                _:rest -> chunk : split c rest
  where (chunk, rest) = break (==c) s

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

setAt :: [a] -> Int -> a -> [a]
setAt xs i x = take i xs ++ [x] ++ drop (i + 1) xs

{-@ modifyAt :: forall a. l: [a] -> {i: Int | i >= 0 && i < len l} -> f: (a -> a) -> [a] @-}
modifyAt :: [a] -> Int -> (a -> a) -> [a]
modifyAt xs i f = take i xs ++ [f $ xs !! i] ++ drop (i + 1) xs

deleteAt :: [a] -> Int -> [a]
deleteAt xs n = take n xs ++ drop (n+1) xs

unzipMaybe :: Maybe (a,b) -> (Maybe a, Maybe b)
unzipMaybe = maybe (Nothing,Nothing) (B.bimap Just Just)

updateLast :: (a -> a) -> [a] -> [a]
updateLast _ [] = []
updateLast f (a : as) = loop a as
  -- Using a helper function to minimize the pattern matching.
  where
  loop a []       = [f a]
  loop a (b : bs) = a : loop b bs

mcons :: Maybe a -> [a] -> [a]
mcons mx xs = maybe xs (:xs) mx

(?:) = mcons
infixr 5 ?:

toMaybe :: Bool -> a -> Maybe a
toMaybe b = if b then Just else const Nothing

notNull :: [a] -> Bool
notNull = not . null

mapSnd :: (a -> b) -> [(c, a)] -> [(c,b)]
mapSnd f = map $ B.second f

mapMSnd :: Monad m => (a -> m b) -> [(c, a)] -> m [(c,b)]
mapMSnd _ [] = return [] 
mapMSnd f ((x,y):xys) = do y'   <- f y 
                           xys' <- mapMSnd f xys  
                           return ((x,y'):xys')