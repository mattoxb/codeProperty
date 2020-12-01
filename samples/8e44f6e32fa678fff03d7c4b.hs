fact :: Integer -> Integer
fact 0 = 1
fact n = helper n 1
    where helper 0 n = n
          helper a n = helper (a-1) n*a