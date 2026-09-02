module RandomUtilities

import System.Random
import Data.Nat
import Data.Vect
import Data.Vect.Sort
import Data.Vect.Elem
import Decidable.Equality
--import Injection
import Complex
import NatRules
import LinearTypes
import public Data.Linear.Notation
import public Data.Linear.Interface
import System
import Data.Linear
import Lemmas


||| Generate a vector of random doubles
export
randomVect : (n : Nat) -> IO (Vect n Double)
randomVect 0 = pure []
randomVect (S k)  = do
  r <- randomRIO (0,2*pi)
  v <- randomVect k
  pure (r :: v)
