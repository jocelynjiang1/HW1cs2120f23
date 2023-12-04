from z3 import *
X = Real('x') #z3 has real numbers
Y = Real('y') #"these strings are just variable names"
s = Solver()
s.add(X**2 + Y**2 ==1) #a method of the solver that can be used to add a constraint to the solver
#adding constraint saying X and Y's respective squares are to add up to 1

if(s.check()==sat):
    m = s.model()
print(m) #question mark at end of Y interpretation given means there's more change afterwards. It does work!

#HOMEWORK EXAMPLES:
sol = Solver()
sol.add(Y>2) #add here is not the mathematical operation but means adding a new constraint.
if(sol.check()==sat):
    m2 = sol.model()
print(m2) #prints y=6, which obviously works.

Z = Real('z')
sol.add(X**2 + Y**2 == Z**2) #Pythagorean theorem
if(sol.check()==sat):
    m3 = sol.model()
print(m3) #model returned, [y = 3, x = 0, z = 3], does work, but IRL, can't have a side length of 0

#add constraint for realistic Pythag theorem:
sol.add(X>0, Y>0, Z>0)
if(sol.check()==sat):
    m4 = sol.model()
print(m4) #model is [y = 46341/16384, x = 2.8284240737?, z = 4]. Basically 8 + 8  = 4^2 if you square first and second args, so it works!


