import random
import scipy.stats as st

class positive():
  def __init__(self, s):
    self.s = s
  
  def __repr__(self):
    return f"p \"{self.s}\""
  def __hash__(self):
    return hash((positive, self.s))
  def __eq__(self, other):
      if isinstance(other, positive):
          return self.s == other.s
      else:
          return False

class negative():
  def __init__(self, s):
    self.s = s
  
  def __repr__(self):
    return f"n \"{self.s}\""
  
  def __hash__(self):
    return hash((negative, self.s))

  def __eq__(self, other):
      if isinstance(other, negative):
          return self.s == other.s
      else:
          return False

alphabet = " abcdefghijklmnopqrstuvwxyz"
# def genNum():
#   r = 1
#   while True:
#     n = random.randint(0,r)
#     if (n == r+1) and (r < len(alphabet)-1):
#       r = r + 1
#     yield n+1
def genNum():
  while True:
    yield st.poisson.rvs(5)+1

def genVar():
  stream = genNum()
  for n in stream:
    yield alphabet[n]

def genLit():
  for each in genVar():
    p = random.randint(0,1)
    if p == 0:
      yield positive(each)
    else:
      yield negative(each)


def genCla():
  for each_length in genNum():
    each_length = each_length+1
    ret = set(map(lambda x: x[1],
               zip(range(each_length),genLit())))
    yield list(ret)
    

def genCNF():
  for each_length in genNum():
    each_length = each_length+1
    yield list(map(lambda x: x[1],
               zip(range(each_length),genCla())))


for (_, cnf) in zip(range(10), genCNF()):
  print(str(cnf).replace(",",";") + ";")


    
    