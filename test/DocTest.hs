module Main (main) where

import Test.DocTest

main :: IO ()
main = doctest ["src/SetTheoryProver/Lib"]