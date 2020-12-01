fact :: Integer -> Integer
fact n = aux n 1
    where aux 1 c = c
          aux b c = aux (b-1) (b*c)