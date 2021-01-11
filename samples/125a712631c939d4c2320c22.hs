fact :: Integer -> Integer
fact 1 = 1
fact n = aux n 1
  where aux 1 prod = prod
        aux a prod = aux (a-1) (a * prod)