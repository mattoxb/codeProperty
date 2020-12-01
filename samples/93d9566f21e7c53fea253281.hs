fact :: Integer -> Integer
fact a = aux a 1
    where aux :: Integer -> Integer -> Integer
          aux 1 m = m
          aux x m = aux (x-1) (m * x)