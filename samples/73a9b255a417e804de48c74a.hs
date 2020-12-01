fact :: Integer -> Integer
fact 0 = 1
fact 1 = 1
fact x = aux 1 x
         where aux n 1 = n
               aux n x = aux (n * x) (x-1)