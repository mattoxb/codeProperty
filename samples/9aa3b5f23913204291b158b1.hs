
fact :: Integer -> Integer
fact 1 = 1
fact n = n * (aux  n 1)
    where
    
    aux n a = if (n-1) > 0
              then aux (n-1) (a*(n-1))
              else n*a
           