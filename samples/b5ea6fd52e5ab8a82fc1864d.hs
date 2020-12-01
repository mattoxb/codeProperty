fact :: Integer -> Integer
fact n = aux n 1
  where 
    aux 0 acc = acc 
    aux 1 acc = acc 
    aux n acc = aux (n - 1) (acc * n)