fact :: Integer -> Integer
fact x = aux x 1
    where aux 0 a = a
          aux x a = aux (x-1) x*a