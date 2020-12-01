fact :: Integer -> Integer
fact n = aux n
    where aux 1 = 1
          aux a = (aux (a-1))*a        