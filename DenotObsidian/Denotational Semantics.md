Goal: conduct proofs of compiler correctness using denotational semantics. Especially the closure conversion pass.

Need to understand correctness for passes that go from higher-level abstractions to lower-level ones, especially where lower-level abstractions are used for multiple different higher-level ones. For example, in closure conversion, we use tuples to represent closures but also use tuples to represent tuples.

We need a way to capture the invariants from the higher-level language in the lower-level one. One possibility is to define a type system that captures the invariants that arise from a low-level program being in the compilation image of the higher level one.

Let's try this on a simple language, without functions, just fractions and pairs.

## Fractions and Pairs (higher-level language)

```
n ::= zero | suc(n)
op ::= + | * | /
e ::= n | e op e              // fractions
    | (e,e) | fst e | snd e   // pairs
T ::= Frac | T x T

--------
n : Frac

e1 : Frac  e2 : Frac
---------------------
e1 op e2 : Frac

e1 : T1 e2 : T2
-------------------
(e1, e2) : T1 x T2

e : T1 x T2
-----------
fst(e) : T1

e : T1 x T2
-----------
snd(e) : T2

Value(Frac) = Real
Value(T1 x T2) = Value(T1) x Value(T2)

[-] : Exp(T) -> Value(T)
[n] = n
[e1 op e2] = [e1] [op] [e2]
[(e1,e2)] = ([e1], [e2])
[fst(e)] = fst([e])
[snd(e)] = snd([e])
```

## Naturals and Pairs (lower-level language)

```
n ::= zero | suc(n)
op ::= + | *
e ::= n | e op e              // natural numbers
    | (e,e) | fst e | snd e   // pairs
    | let x = e in e
T ::= Nat | T x T

--------
n : Nat

e1 : Nat  e2 : Nat
---------------------
e1 op e2 : Nat

e1 : T1 e2 : T2
-------------------
(e1, e2) : T1 x T2

e : T1 x T2
-----------
fst e : T1

e : T1 x T2
-----------
snd e : T2

Value(Nat) = Nat
Value(T1 x T2) = Value(T1) x Value(T2)

[-] : Exp(T) -> Value(T)
[n] = n
[e1 op e2] = [e1] [op] [e2]
[(e1,e2)] = ([e1], [e2])
[fst(e)] = fst([e])
[snd(e)] = snd([e])
```

## Compilation

```
Ctype : T -> T
Ctype(Frac) = = Nat x Nat
Ctype(T1 x T2) = Ctype(T1) x Ctype(T2)

C : Exp(T) -> Exp(Ctype(T))
C(n) = (n,1)
C(e1 + e2) = (snd(y) * fst(x) + snd(x) * fst(y), snd(x) * snd(y))
             where x = C(e1) and y = C(e2)
C(e1 * e2) = (fst(e1) * fst(e1), snd(e1) * snd(e2))
             where x = C(e1) and y = C(e2)
C(e1 / e2) = (fst(e1) * snd(e2), fst(e2) * snd(e1))
             where x = C(e1) and y = C(e2)
C((e1,e2)) = (C(e1), C(e2))
C(fst(e)) = fst(C(e))
C(snd(e)) = snd(C(e))
```

## Correctness

The following is a logical relation that expresses when denotational values from the two languages are equivalent.

```
=@T : Value(T) x Value(Ctype(T)) -> bool
r =@Frac (v1,v2)             if r = v1/v2
(v1,v2) =@(T1 x T2) (v3,v4)  if v1 =@T1 v3  and v2 =@T2 v4
```

```
theorem [Correctness] if e : T then [e] =@T [C(e)]
proof
  induction on e : T
  case --------
       n : Frac
    [n] = n
    C(n) = (n,1)
    [(n,1)] = (n,1)
    n =@Frac (n,1) because n = n/1
    
  case e1 : Frac  e2 : Frac
       -------------------- IH1: [e1] =@Frac [C(e1)], IH2: [e2] =@Frac [C(e2)]
          e1 + e2 : Frac
    have IH1': [e1] = r1, [C(e1)] = (v1,v2) and r1 = v1/v2
    have IH2': [e2] = r2, [C(e2)] = (v3,v4) and r2 = v3/v4
    
    [e1 + e1] = [e1] [+] [e2]
    C(e1 + e2) = (snd(y) * fst(x) + snd(x) * fst(y), snd(x) * snd(y))
                 where x = C(e1) and y = C(e2)
    [e1] [+] [e2] =@Frac [C(e1+e2)]
                  =@Frac [(snd(y) * fst(x) + snd(x) * fst(y), snd(x) * snd(y))]
                  =@Frac (snd([y]) * fst([x]) + snd([x]) * fst([y]),
                          snd([x]) * snd([y]))]
                  =@Frac (v4 * v1 + v2 * v3, v2 * v4)]
    if v1/v2 + v3/v4 = (v1*v4)/(v2*v4) + (v3*v2)/(v4*v2)
                     = (v4 * v1 + v2 * v3) / (v2 * v4)
  case e1 : Frac  e2 : Frac
       --------------------
          e1 * e2 : Frac
          
  case e1 : Frac  e2 : Frac
       --------------------
          e1 / e2 : Frac
          
  case e1 : T1 e2 : T2
       ------------------- IH1: [e1] =@T1 [C(e1)], IH2: [e2] =@T2 [C(e2)]
       (e1, e2) : T1 x T2
    [(e1,e2)] = ([e1],[e2])
    [C(e1,e2)] = ([C(e1)],[C(e2)])
    ([e1],[e2]) =@(T1 x T2) ([C(e1)],[C(e2)])

  case e : T1 x T2
       ----------- IH: [e] =@(T1xT2) [C(e)]
       fst e : T1
    have [e] = (v1,v2), [C(e)] = (v3,v4), v1 =@T1 v3, v2 =@T2 v4 by IH
    [fst(e)] = fst([e]) = v1
    [C(fst(e))] = [fst(C(e))] = fst([C(e)]) = v3
    conclude v1 =@T1 v3
    
  case e : T1 x T2
       -----------
       snd e : T2
    have [e] = (v1,v2), [C(e)] = (v3,v4), v1 =@T1 v3, v2 =@T2 v4 by IH
    [snd(e)] = snd([e]) = v2
    [C(snd(e))] = [snd(C(e))] = snd([C(e)]) = v4
    conclude v2 =@T2 v4
end
```