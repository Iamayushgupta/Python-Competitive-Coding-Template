#  _______  __   __  __   __  _______  __   __
# |   _   ||  | |  ||  | |  ||       ||  | |  |
# |  |_|  ||  |_|  ||  | |  ||  _____||  |_|  |
# |       ||       ||  |_|  || |_____ |       |
# |       ||_     _||       ||_____  ||       |
# |   _   |  |   |  |       | _____| ||   _   |
# |__| |__|  |___|  |_______||_______||__| |__|
#  _______  __   __  _______  _______  _______
# |       ||  | |  ||       ||       ||   _   |
# |    ___||  | |  ||    _  ||_     _||  |_|  |
# |   | __ |  |_|  ||   |_| |  |   |  |       |
# |   ||  ||       ||    ___|  |   |  |       |
# |   |_| ||       ||   |      |   |  |   _   |
# |_______||_______||___|      |___|  |__| |__|

from bisect import bisect_left
from bisect import bisect_right
import re
import math as mt
from tempfile import tempdir
from traceback import print_tb
from typing import DefaultDict
import math
from collections import Counter, defaultdict
from math import sqrt
import collections
from sys import maxsize
from itertools import combinations_with_replacement
import heapq
from collections import deque
import sys

def sieve_erasthones(n):
    # prime number less than equal to n
    # complexixty n*log(log(n))
    cnt = 0
    prime = [True for i in range(n+1)]
    p = 2
    while (p*p <= n):
        if (prime[p] == True):
            for i in range(p**2, n+1, p):
                prime[i] = False
        p += 1
    prime[0] = False
    prime[1] = False
    # for p in range(n+1):
    #     if prime[p]:
    #         cnt += 1
    # return cnt
    return prime

def calculate(p, q):
    mod = 998244353
    expo = 0
    expo = mod - 2
    while (expo):
        if (expo & 1):
            p = (p*q) % mod
        q = (q*q) % mod
        expo >>= 1
    return p

def count_factors(n):
    i = 1
    c = 0
    ans = []
    while i <= math.sqrt(n):
        if n % i == 0:
            if n//i == i:
                c += 1
                ans.append(n//i)
            else:
                c += 2
                ans.append(i)
                ans.append(n//i)
        i += 1
    # return c
    return ans

def ncr_modulo(n, r, p):
    num = 2
    den=1
    for i in range(r):
        num = (num * (n - i)) % p
        den = (den * (i + 1)) % p
    return (num * pow(den,
                      p - 2, p)) % p

def isprime(n):
    prime_flag = 0
    if(n > 1):
        for i in range(2, int(sqrt(n)) + 1):
            if (n % i == 0):
                prime_flag = 1
                break
        if (prime_flag == 0):
            return True
        else:
            return False
    else:
        return True


def smallestDivisor(n):
    if (n % 2 == 0):
        return 2
    i = 3
    while(i * i <= n):
        if (n % i == 0):
            return i
        i += 2
    return n


def modular_exponentiation(x, y, p):
    res = 1
    x = x % p
    if x == 0:
        return 0

    while (y > 0):
        if ((y & 1) != 0):
            res = (res * x) % p
        y = y >> 1
        x = (x * x) % p

    return res


def number_of_primefactor(n):
    l = []
    while n % 2 == 0:
        l.append(2)
        n = n / 2

    for i in range(3, int(math.sqrt(n))+1, 2):
        while (n % i == 0):
            l.append(i)
            n = n / i
    if n > 2:
        l.append(n)
    return l


def twosum(a, n, x):
    rem = []
    for i in range(x):
        rem.append(0)
    for i in range(n):
        if (a[i] < x):
            rem[a[i] % x] += 1
    for i in range(1, x // 2):
        if (rem[i] > 0 and rem[x - i] > 0):
            return True
    if (i >= x // 2):
        if (x % 2 == 0):
            if (rem[x // 2] > 1):
                return True
            else:
                return False
        else:
            if (rem[x // 2] > 0 and
                    rem[x - x // 2] > 0):
                return True
            else:
                return False

def divSum(num):
    result = 0
    i = 2
    while i <= (math.sqrt(num)):
        if (num % i == 0):
            if (i == (num / i)):
                result = result + i
            else:
                result = result + (i + num/i)
        i = i + 1
    return (result + 1 + num)

def subsequence(str1, str2):
    # check if s1 is a subsequence of s2
    m = len(str1)
    n = len(str2)

    j = 0    # Index of str1
    i = 0    # Index of str2
    while j < m and i < n:
        if str1[j] == str2[i]:
            j = j+1
        i = i + 1
    return j == m

def primeFactors(n):
    d = defaultdict(lambda: 0)
    while n % 2 == 0:
        d[2] += 1
        n = n / 2

    for i in range(3, int(math.sqrt(n))+1, 2):

        while n % i == 0:
            d[int(i)] += 1
            n = n / i
    if n > 2:
        d[int(n)] += 1

    return d

def lcm(a, b):
    return a*b//(math.gcd(a, b))

def modInverse(b, m):
    return pow(b, m - 2, m)

def modDivide(a, b, m):
    a = a % m
    inv = modInverse(b, m)
    return (inv*a) % m

def subarrayXor(arr, n, m):

	ans = 0 

	xorArr =[0 for _ in range(n)]

	mp = dict()

	xorArr[0] = arr[0]

	for i in range(1, n):
		xorArr[i] = xorArr[i - 1] ^ arr[i]

	for i in range(n):
		
		tmp = m ^ xorArr[i]

		if tmp in mp.keys():
			ans = ans + (mp[tmp])

		if (xorArr[i] == m):
			ans += 1

		mp[xorArr[i]] = mp.get(xorArr[i], 0) + 1

	return ans

def lcs(X, Y):
    m = len(X)
    n = len(Y)
    L = [[None]*(n + 1) for i in range(m + 1)]
    for i in range(m + 1):
        for j in range(n + 1):
            if i == 0 or j == 0 :
                L[i][j] = 0
            elif X[i-1] == Y[j-1]:
                L[i][j] = L[i-1][j-1]+1
            else:
                L[i][j] = max(L[i-1][j], L[i][j-1])
    return L[m][n]


def solve(t):
    # vowels="aeiou"
    n=int(input())
    # n,x1,y1,x2,y2=map(int,input().split())
    # x,y=map(int,input().split())
    # n,q=input().split()
    # s1,s2=input().split()
    # s=input()
    # mod=1000000007
    # mod=998244353
    # d=defaultdict(lambda:0) 
    # l=list(map(int,input().split()))


    #For google-kickstart
    # print("Case #" + str(t) + ":", end=" ")
    
for t in range(1, int(input())+1):
    # solve(t)
    print(solve(t))

# t = 1
# print(solve(t))
 



	
