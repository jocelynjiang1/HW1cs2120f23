from z3 import *

# PUZZLES

# These puzzles are borrowed from EricPony Z3 Python Tutorial 

# OneHundredAnimals
# You must spend exactly 100 dollars and buy exactly 100 animals. 
# Dogs cost 15 dollars, cats cost 1 dollar, and mice cost 25 cents. 
# You have to buy at least one of each. How many of each should 
# you buy?
print("")
print("How many dogs, cats, mice should you buy?")

# Integer values TBD: how many of each to buy? Followed by
# constraints on solution imposed by problem formulation. 
dog, cat, mouse = Ints('dog cat mouse') 
solve(dog >= 1,   
      cat >= 1,   
      mouse >= 1, #first set of constraints^: must buy at least one of each
      dog + cat + mouse == 100, #second constraint^: #to buy 100 animals, not supposed to buy more or fewer
      1500 * dog + 100 * cat + 25 * mouse == 10000) #budget is 10000 cents ($100), total cost cannot exceed
#written in form 1500 and 100 to accommodate 25 cents per mice: so cents are the unit
# How would you solve this with a Python program?
