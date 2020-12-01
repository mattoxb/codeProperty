fact :: Integer -> Integer
fact 0 = 1
fact a = aux a 1
  where
    aux 0 c = c
    aux b c = aux (b-1) b*c