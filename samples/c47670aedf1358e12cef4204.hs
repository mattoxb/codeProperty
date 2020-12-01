fact :: Integer -> Integer
fact x = aux x 1
  where aux 0 a = a
        aux b a = aux(b-1) (a * b)
