from z3 import *

### Eight Queens

print("Eight Queens")
# We know each queen must be in a different row.
# So, we represent each queen by a single integer: the column position
Q = [ Int('Q_%i' % (i + 1)) for i in range(8) ] #we're not modeling the gameboard but the queens' positions
#remember from Java: the % is not modulo but equivalent of "printf flag" in Java

# Each queen is in a column {1, ... 8 }
val_c = [ And(1 <= Q[i], Q[i] <= 8) for i in range(8) ] #we have 1 Q[i] per column

# At most one queen per column
col_c = [ Distinct(Q) ] #in each column, there should be at most one True (one queen per column at most). Every queen has to be different

# Diagonal constraint
diag_c = [ If(i == j,
              True,
              And(Q[i] - Q[j] != i - j, Q[i] - Q[j] != j - i)) #for no two squares can the AND of them be true
           for i in range(8) for j in range(i) ]
#basically, no two queens are in same column, no two queens are on same diagonal

solve(val_c + col_c + diag_c) #"a specification, not a program"
