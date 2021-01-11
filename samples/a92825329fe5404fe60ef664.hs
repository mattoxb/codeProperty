fact :: Integer -> Integer
fact n = aux 1 n
  where
    aux factorial n
      | n <= 1 = factorial
      | otherwise = aux (factorial * n) (n - 1)
