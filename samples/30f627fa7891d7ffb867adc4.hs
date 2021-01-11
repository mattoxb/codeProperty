fact :: Integer -> Integer
fact x = aux x 1
    where aux 0 y = y
          aux x y = aux (x-1) (x*y)