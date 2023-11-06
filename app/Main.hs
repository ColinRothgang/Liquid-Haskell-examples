module Main where

import Prelude
import System.Environment(getArgs)
import LHToCoq(run)

main :: IO ()
main = getArgs >>= run