fact :: Integer -> Integer
fact val = (helper val 1) where 
helper 0 accum = accum
helper val accum = helper (val-1) accum*val