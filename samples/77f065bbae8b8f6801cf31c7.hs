fact :: Integer -> Integer
fact 0 = 1
fact n = aux n 1
  where aux 0 a = a
        aux n a = aux (n - 1) (n * a)