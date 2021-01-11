fact :: Integer -> Integer
fact n = aux 1 n
    where aux ml 1 = ml
          aux ml n = aux (ml * n) (n - 1)